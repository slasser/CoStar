import matplotlib
matplotlib.use('Agg')
import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter
from sys import argv
from statsmodels.nonparametric.smoothers_lowess import lowess as lowess
import math

datafile = argv[1]
plotfile = argv[2]

with open(datafile, "r") as fh:
    test_results      = json.load(fh)

# keep the bottom 99% of data points
drop = int(len(test_results) * 0.99)
test_results = test_results[0:drop]

token_counts      = [int(tr["num_tokens"])   for tr in test_results]
parse_time_groups = [[float(pt) for pt in tr["parse_times"]] for tr in test_results]

avg_parse_times = [np.mean(g) for g in parse_time_groups]

fig = plt.figure(figsize=(3.8, 1.7))
ax = fig.add_subplot(111)

sizes = np.array(token_counts, np.int)
times = np.array(avg_parse_times, np.float)
plt.scatter(sizes,times,s=5,color='#6a86d9')

# lin regression line
fit = np.polyfit(sizes, times, deg=1)
fit_fn = np.poly1d(fit)
p1 = plt.plot(sizes, fit_fn(sizes), 'k--', lw=1.5)

# lowess line
z = lowess(times, sizes, frac=0.1)
p2 = plt.plot(z[:,0], z[:,1], '-', lw = 1.5, color = 'r', label = "Lowess fit")

if (datafile=="dot__costar-parser.json"):
    l1 = plt.Line2D([0,0], [1,1], color='k', linestyle='--')
    l2 = plt.Line2D([0,0], [1,1], color='r')
    plt.legend([l1,l2], ["Regression", "LOWESS"],prop={'size':11}, loc='lower right')

lang = ""
if datafile == "json__costar-parser.json":
    lang = "JSON files"
elif datafile == "xml__costar-parser.json":
    lang = "XML files"
elif datafile == "dot__costar-parser.json":
    lang = "DOT files"
elif datafile == "python__costar-parser.json" or datafile == "python__antlr-parser.json"  or datafile == "python__antlr-parser__cache-warm-up.json":
    lang = "Python files"

print(max(times)/1.5)
plt.text(max(sizes)/130.0, 0.02467, "%d %s"%(len(test_results),lang), family="serif", size=14)

plt.setp(ax.get_xticklabels(), fontsize=14)
plt.setp(ax.get_yticklabels(), fontsize=14)
plt.gca().get_xaxis().set_major_formatter(FuncFormatter(lambda x, p: format(int(round(x / 1000)), ',')))

ax.set_title("ANTLR parser, after cache warm-up")
plt.ylim([0.0, 0.04])
plt.savefig(plotfile, format="eps", bbox_inches='tight', pad_inches=0, dpi=1000)
print ("results saved to evaluation/results/" + plotfile)
