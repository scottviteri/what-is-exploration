#!/usr/bin/env python3
"""Plot a saved policy comparison and the symmetric commitment calculation."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np


HERE = Path(__file__).resolve().parent


def main():
    data = json.loads((HERE / 'results.json').read_text())
    case = next(c for c in data['cases'] if c['name'] == 'sensors_0.1_0.3')
    selected = {
        objective: next(s for s in case['cross_scores']
                        if s['objective'] == objective and s['fraction'] == 0)
        for objective in ['native_weighted', 'brier']
    }
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.7), layout='constrained')
    colors = ['#007F86', '#A64B20']

    ax = axes[0]
    positions = np.arange(4)
    for index, (objective, label) in enumerate([
            ('native_weighted', 'Native weighted'), ('brier', 'Brier')]):
        record = selected[objective]
        values = 100 * np.array(record['each'][:3] + [record['mean']])
        bars = ax.bar(positions + (index - .5) * .36, values,
                      width=.36, color=colors[index], label=label)
        ax.bar_label(bars, labels=[f'{v:.1f}' for v in values], padding=3, fontsize=9)
    ax.set_xticks(positions, ['Guess U', 'Guess V', 'Parity', 'Mean of 7'])
    ax.set_ylim(50, 103)
    ax.set_yticks(np.arange(50, 101, 10))
    ax.set_ylabel('Best downstream accuracy (%)')
    ax.set_title('Unequal sensor quality: a capability tradeoff\nL error 10%, R error 30%; three actions', fontsize=11)
    ax.legend(loc='upper right', frameon=False, fontsize=9)

    ax = axes[1]
    alpha = np.linspace(0, 1, 201)
    known_bit_accuracy = .9**3 + 3 * .9**2 * .1
    ax.plot(alpha, 100 * (.5 + (known_bit_accuracy - .5) * alpha),
            color=colors[0], label='Guess U', linewidth=2)
    ax.plot(alpha, 100 * (.5 + (known_bit_accuracy - .5) * (1-alpha)),
            color=colors[1], label='Guess V', linewidth=2)
    mean = (known_bit_accuracy + .5 + .5 + 4 * .75) / 7
    ax.axhline(100 * mean, color='#343A40', linestyle='--', linewidth=2,
               label='Mean of 7')
    ax.axvline(.5, color='#888888', linestyle=':', linewidth=1.5)
    ax.plot(.5, 100 * (.5 + (known_bit_accuracy - .5) / 2),
            'o', color='#343A40', markersize=6)
    ax.annotate('Native balances here\n73.6% on either bit',
                (.5, 73.6), xytext=(.51, 85), fontsize=9, ha='center',
                arrowprops={'arrowstyle': '-', 'color': '#666666'})
    ax.text(.98, 69, 'Mean stays at 71.03%', ha='right', fontsize=9)
    ax.set_xlim(0, 1)
    ax.set_ylim(50, 103)
    ax.set_yticks(np.arange(50, 101, 10))
    ax.set_xlabel('Probability of committing to U')
    ax.set_title('Irreversible choice: the average hides allocation\nBoth errors 10%; three readings of the chosen bit', fontsize=11)
    ax.legend(loc='lower center', ncols=3, frameon=False, fontsize=9)
    for ax in axes:
        ax.spines[['top', 'right']].set_visible(False)
        ax.grid(axis='y', color='#DDDDDD', linewidth=.5)
        ax.set_axisbelow(True)
    fig.savefig(HERE / 'capability_tradeoffs.png', dpi=180)
    fig.savefig(HERE / 'capability_tradeoffs.pdf')


if __name__ == '__main__':
    main()
