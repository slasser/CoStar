import matplotlib
matplotlib.use('Agg')
import json
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter
from sys import argv
from statsmodels.nonparametric.smoothers_lowess import lowess as lowess
import math
import os

# avoid Type 3 fonts (required for camera-ready copy)
matplotlib.rcParams['pdf.fonttype'] = 42
matplotlib.rcParams['ps.fonttype']  = 42

datafile          = argv[1]
datafile_basename = os.path.basename(datafile)
plotfile          = argv[2]

with open(datafile, "r") as fh:
    test_results      = json.load(fh)

# keep the bottom 99% of data points
# drop = int(len(test_results) * 0.99)
# test_results = test_results[0:drop]

token_counts      = [int(tr["num_tokens"])   for tr in test_results]
parse_time_groups = [[float(pt) for pt in tr["execution_times"]] for tr in test_results]

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
z = lowess(times, sizes, frac=0.3)
p2 = plt.plot(z[:,0], z[:,1], '-', lw = 1.5, color = 'r', label = "Lowess fit")

# legend
if (datafile_basename == "json_results.json"):
    l1 = plt.Line2D([0,0], [1,1], color='k', linestyle='--')
    l2 = plt.Line2D([0,0], [1,1], color='r')
    plt.legend([l1,l2], ["Regression", "LOWESS"],prop={'size':11}, loc='lower right')

# text that lists number of data points (e.g., "24 JSON files")
lang = ""
if datafile_basename.split("_")[0] == "json":
    lang = "JSON"
elif datafile_basename.split("_")[0] == "xml":
    lang = "XML"
elif datafile_basename.split("_")[0] == "ppm":
    lang = "PPM"
elif datafile_basename.split("_")[0] == "newick":
    lang = "Newick"

plt.text(max(sizes)/13.0, max(times)/1.5, "%d %s files"%(len(test_results),lang), family="serif", size=14)

# increase font size of tick labels
plt.setp(ax.get_xticklabels(), fontsize=14)
plt.setp(ax.get_yticklabels(), fontsize=14)

# divide x-axis values by 1000 (convert tokens to "thousands of tokens")
plt.gca().get_xaxis().set_major_formatter(FuncFormatter(lambda x, p: format(int(round(x / 1000)), ',')))

# make x and y axes start at zero
ax.set_xlim([0, None])
ax.set_ylim([0, None])

plt.savefig(plotfile, format="pdf", bbox_inches='tight', pad_inches=0, dpi=1000)
print ("results saved to " + plotfile)
