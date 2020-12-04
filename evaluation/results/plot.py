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
std_devs        = [np.std(g) for g in parse_time_groups]

# print standard deviation info
max_std_dev = max(std_devs)
max_std_dev_i = std_devs.index(max_std_dev)
print("largest std dev: " + str(max_std_dev))
print("mean for data point w/largest std dev: " + str(avg_parse_times[max_std_dev_i]))

fig = plt.figure(figsize=(3.8, 1.7))
ax = fig.add_subplot(111)

sizes = np.array(token_counts, np.int)
times = np.array(avg_parse_times, np.float)
plt.scatter(sizes,times,s=2,color='#6a86d9')

# lin regression line
fit = np.polyfit(sizes, times, deg=1)
fit_fn = np.poly1d(fit)
p1 = plt.plot(sizes, fit_fn(sizes), 'k--', lw=1.2)

# lowess line
z = lowess(times, sizes, frac=0.1)
p2 = plt.plot(z[:,0], z[:,1], '-', lw = 1.2, color = 'r', label = "Lowess fit")

if (datafile=="dot.json"):
    l1 = plt.Line2D([0,0], [1,1], color='k', linestyle='--')
    l2 = plt.Line2D([0,0], [1,1], color='r')
    plt.legend([l1,l2], ["Regression", "LOWESS"],prop={'size':11}, loc='lower right')

lang = ""
if datafile == "json-nobel.json":
    lang = "JSON"
elif datafile == "xml-plos.json":
    lang = "XML"
elif datafile == "dot.json":
    lang = "DOT"
elif datafile == "python3.json":
    lang = "Python3"        
plt.text(max(sizes)/13, max(times)/1.5, "%d %s files"%(len(test_results),lang), family="serif", size=14)

plt.gca().get_xaxis().set_major_formatter(FuncFormatter(lambda x, p: format(int(round(x / 1000)), ',')))

plt.savefig(plotfile, format="eps", bbox_inches='tight', pad_inches=0, dpi=1000)
print ("results saved to " + plotfile)
