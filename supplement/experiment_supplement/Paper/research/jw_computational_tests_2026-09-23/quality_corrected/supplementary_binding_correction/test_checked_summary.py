"""Synthetic acceptance/corruption checks; reads no confirmation outcomes."""
from pathlib import Path
import csv, hashlib, json, sys, tempfile, unittest
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from checked_summary import checked_summary, csv_scalar, verify_unchanged

class BindingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.summary = self.root / 'summary'
        self.summary.mkdir()
        self.path = self.summary / 'summary.json'
        self.check = self.root / 'SUMMARY_CHECK.json'
        self.rows = [dict(model='m', method='fixed', budget_seconds=40,
                         flag=True, zero=0.0, missing=None, notes=['a','b'])]
        self.write_json()
        with (self.summary/'endpoints.csv').open('w', newline='') as stream:
            writer=csv.DictWriter(stream,fieldnames=list(self.rows[0]))
            writer.writeheader()
            writer.writerows({k:csv_scalar(v) for k,v in row.items()} for row in self.rows)
        self.bind()
    def write_json(self):
        self.path.write_text(json.dumps({'metadata':{'status':'final_snapshot'},'endpoints':self.rows}))
    def bind(self):
        self.check.write_text(json.dumps({'status':'passed','errors':[],
            'input_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in [self.path,self.summary/'endpoints.csv']}}))
    def reject(self):
        with self.assertRaises(ValueError):checked_summary(self.path)
    def test_valid_mixed_serialization(self):
        report,bindings=checked_summary(self.path)
        self.assertEqual(report['endpoints'],self.rows)
        verify_unchanged(bindings)
    def test_json_mutation_with_stale_checker(self):
        self.rows[0]['zero']=1.0;self.write_json();self.reject()
    def test_json_mutation_with_refreshed_hash(self):
        self.rows[0]['zero']=1.0;self.write_json();self.bind();self.reject()
    def test_missing_checker_coverage(self):
        record=json.loads(self.check.read_text());record['input_sha256'].pop(str(self.path))
        self.check.write_text(json.dumps(record));self.reject()
    def test_duplicate_key(self):
        self.rows*=2;self.write_json();self.bind();self.reject()
    def test_extra_json_column(self):
        self.rows[0]['unvalidated']='x';self.write_json();self.bind();self.reject()
    def test_errors_despite_passed_status(self):
        record=json.loads(self.check.read_text());record['errors']=['bad']
        self.check.write_text(json.dumps(record));self.reject()
    def test_subsequent_change_detected(self):
        _,bindings=checked_summary(self.path)
        self.check.write_text(self.check.read_text()+' ')
        with self.assertRaises(ValueError):verify_unchanged(bindings)
    def test_csv_change_rejected(self):
        p=self.summary/'endpoints.csv';p.write_text(p.read_text().replace('fixed','minimax'))
        self.bind();self.reject()

if __name__=='__main__':unittest.main(verbosity=2)
