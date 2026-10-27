"""Draw Figure 1 with Matplotlib's BaKoMa Computer Modern Sans font."""
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle


def main():
    root = Path(__file__).resolve().parent
    data = json.loads((root / 'repair-example.json').read_text())
    matplotlib.rcParams.update({'font.family': 'cmss10', 'font.size': 9,
                                'mathtext.fontset': 'cm',
                                'svg.fonttype': 'path', 'pdf.fonttype': 42})
    fig, ax = plt.subplots(figsize=(10.0, 4.0))
    ax.set_xlim(-3.1, 16.5)
    ax.set_ylim(-3.65, 4.1)
    ax.axis('off')
    orange, blue = '#f1c89c', '#c9e0ed'
    for i in range(16):
        ax.text(i + .5, 3.2, str(i + 1), ha='center', va='center', fontsize=8)
    ax.text(-.3, 3.2, 'Position', ha='right', va='center')
    for row, y, title in [('sorted_word', 2.1, 'Sorted'),
                          ('repaired_word', .35, 'Repaired')]:
        ax.text(-.3, y + .4, title, ha='right', va='center')
        for i, label in enumerate(data[row]):
            color = orange if label == 1 else blue if label == 2 else 'white'
            ax.add_patch(Rectangle((i, y), 1, .8, facecolor=color,
                                   edgecolor='#333333', linewidth=.65))
            ax.text(i + .5, y + .4, data['labels'][label], ha='center', va='center')
        b = [i + .5 for i, label in enumerate(data[row]) if label == 1]
        ax.annotate('', (b[1], y - .25), (b[0], y - .25),
                    arrowprops={'arrowstyle': '<->', 'color': '#87501e', 'linewidth': 1})
        gap = int(b[1] - b[0])
        ax.text(sum(b) / 2, y - .57, f'B: gap {gap}' + (r' $>$ 6' if gap > 6 else ' = 6'),
                ha='center', va='center', color='#87501e', fontsize=8)
    ax.text(-.3, -2.2, 'Calendar', ha='right', va='center')
    x0, cell = 1.0, 1.4
    for col, label in enumerate(data['labels'][2:]):
        ax.text(x0 + (col + .5) * cell, -1.5, label, ha='center', va='center')
        for machine in range(2):
            y = -2.15 - machine * .65
            filled = machine == 0 and col == 0
            ax.add_patch(Rectangle((x0 + col * cell, y), cell, .55,
                                   facecolor=orange if filled else 'white',
                                   edgecolor='#555555', linewidth=.65))
            if filled:
                ax.text(x0 + .5 * cell, y + .275, 'B', ha='center', va='center')
    ax.text(x0, -3.1, 's = 0', ha='center', va='center', fontsize=8)
    ax.text(x0 + cell, -3.1, 'e = 1', ha='center', va='center', fontsize=8)
    ax.text(10.3, -2.2, 'Capacity: 2 per column\nJob length: 1\nP: C B D E F G H\nQ: B C D E F G H',
            ha='left', va='center', linespacing=1.5)
    fig.subplots_adjust(left=.01, right=.99, top=.99, bottom=.01)
    for suffix in ('pdf', 'svg', 'png'):
        fig.savefig(root / f'repair-example.{suffix}', dpi=180,
                    metadata={'Creator': 'Matplotlib'} if suffix == 'pdf' else None)
    plt.close(fig)
    print(f'Figure 1 generated with Matplotlib {matplotlib.__version__}')


if __name__ == '__main__':
    main()
