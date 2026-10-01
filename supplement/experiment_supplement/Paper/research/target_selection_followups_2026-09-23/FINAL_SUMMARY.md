# Completed follow-up execution: outcome and remaining gaps

Updated 2026-09-23T20:49:03.492274+00:00.

The original run remains unchanged. This report combines only results with completed saved-certificate or explicit-witness checks.

## Execution

- completion_results: {'status': 'finished', 'counts': {'complete': 17}, 'started_utc': '2026-09-23T18:47:53.662990+00:00', 'finished_utc': '2026-09-23T19:12:05.376877+00:00'}
- recovery_results: {'status': 'finished', 'counts': {'complete_verified': 4, 'failed': 1}, 'started_utc': '2026-09-23T18:51:47.862134+00:00', 'finished_utc': '2026-09-23T19:39:09.933535+00:00'}
- near_optimal_results: {'status': 'finished', 'counts': {'complete_verified': 70}, 'started_utc': '2026-09-23T19:39:15.115605+00:00', 'finished_utc': '2026-09-23T20:48:15.796348+00:00'}

Completed jobs awaiting their separate certificate audit: [].

## Held-out n=4 comparison (collector t=3)

| Native method | Comparator | Cases | Wins / ties / losses / mixed |
|---|---|---:|---|
| minimax | information | 22 | 21 / 1 / 0 / 0 |
| minimax | brier | 22 | 19 / 1 / 2 / 0 |
| minimax | pseudo_count | 22 | 20 / 1 / 1 / 0 |
| minimax | legacy_native_weighted | 20 | 14 / 1 / 5 / 0 |
| minimax | face_information_0 | 22 | 21 / 1 / 0 / 0 |
| minimax | face_information_0.01 | 17 | 16 / 1 / 0 / 0 |
| minimax | face_information_0.05 | 18 | 18 / 0 / 0 / 0 |
| minimax | face_brier_0 | 22 | 20 / 1 / 1 / 0 |
| minimax | face_brier_0.01 | 18 | 16 / 1 / 1 / 0 |
| minimax | face_brier_0.05 | 17 | 15 / 0 / 2 / 0 |
| weighted128 | information | 22 | 20 / 1 / 1 / 0 |
| weighted128 | brier | 22 | 18 / 2 / 2 / 0 |
| weighted128 | pseudo_count | 22 | 20 / 1 / 1 / 0 |
| weighted128 | legacy_native_weighted | 20 | 10 / 0 / 10 / 0 |
| weighted128 | face_information_0 | 22 | 20 / 1 / 1 / 0 |
| weighted128 | face_information_0.01 | 17 | 15 / 0 / 2 / 0 |
| weighted128 | face_information_0.05 | 18 | 15 / 0 / 3 / 0 |
| weighted128 | face_brier_0 | 22 | 19 / 1 / 2 / 0 |
| weighted128 | face_brier_0.01 | 18 | 14 / 0 / 4 / 0 |
| weighted128 | face_brier_0.05 | 17 | 13 / 0 / 4 / 0 |

These are descriptive case counts, with numerical envelopes across available policy representatives. Missing cases are not wins or zero errors. The fixed weighted objective and minimax are finite; changes of selected optimum can affect held-out performance.

COMBINED_STATUS.json retains exact comparison intervals and source/verification paths. Historical predictive/label-entropy results remain in the original archive, outside the current source-aligned figure methods.


This dated report was frozen after the registered queues stopped. Terminal queue counts identify any failed, skipped or unavailable work; “finished” does not imply every planned case succeeded. All original and follow-up failures remain visible. The near-optimal extension began with 70 available policies out of 88 originally registered. No new manuscript integration, commit, push or export is performed.
