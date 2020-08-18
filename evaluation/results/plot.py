import matplotlib
matplotlib.use('Agg')
import json
import numpy as np
import matplotlib.pyplot as plt
from sys import argv

datafile = argv[1]
plotfile = argv[2]

with open(datafile, "r") as fh:
    test_results = json.load(fh)
    token_counts = [int(tr["num_tokens"])   for tr in test_results]
    parse_times  = [float(tr["parse_time"]) for tr in test_results]

print token_counts
print parse_times

plt.figure(figsize=(13.5, 5))

width = max(token_counts) / len(token_counts) / 2
bars  = plt.bar(token_counts, parse_times, width)

plt.xlabel("Number of tokens")
plt.ylabel("Time (s)")

plt.savefig(plotfile, format="eps", dpi=1000)

"""with open(datafile, "r") as fh:
    d = json.load(fh)
    fileSizes = [int(s)/1000.0 for s in d["file_sizes"]]
    lexerTimes = [float(s) for s in d["lexer_times"]]
    parserTimes = [float(s) for s in d["parser_times"]]



print(fileSizes)
print(lexerTimes)
print(parserTimes)

N = len(fileSizes)

ind = np.arange(N)    # the x locations for the groups
width = 20       # the width of the bars: can also be len(x) sequence

plt.figure(figsize=(13.5, 5))

# p1 = plt.bar(fileSizes, menhirParserTimes, width)
p2 = plt.bar([fs + width for fs in fileSizes], lexerTimes, width)
p3 = plt.bar([fs + width for fs in fileSizes], parserTimes, width, bottom = lexerTimes)


plt.xlabel("File Size (KB)")
plt.ylabel("Time (s)")

#plt.xticks(fileSizes, [str(fs) for fs in fileSizes])
plt.legend((p2[0], p3[0]), ("Menhir Tokenizer", "ALL(*) Parser"))
#plt.yticks(np.arange(0, 81, 10))
#plt.legend((p1[0], p2[0]), ('Men', 'Women'))
plt.savefig(plotfile, format="eps", dpi=1000)
"""
