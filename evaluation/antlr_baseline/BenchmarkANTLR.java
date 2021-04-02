import java.io.*;
import java.util.*;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import org.antlr.v4.runtime.atn.ParserATNSimulator;
import org.antlr.v4.tool.*;
import org.json.*;

public class BenchmarkANTLR {

    enum Benchmark      { JSON, XML, DOT, PYTHON }
    enum ANTLRComponent { LEXER, PARSER }

    static String JSON_GRAMMAR        = "JSON.g4";
    static String JSON_START_SYM      = "json";

    static String DOT_GRAMMAR         = "DOT.g4";
    static String DOT_START_SYM       = "graph";

    static String PYTHON_GRAMMAR      = "Python3.g4";
    static String PYTHON_START_SYM    = "file_input";

    static String XML_LEXER_GRAMMAR   = "XMLLexer.g4";
    static String XML_PARSER_GRAMMAR  = "XMLParser.g4";
    static String XML_START_SYM       = "document";

    static String FILENAME_KEY        = "filename";
    static String NUM_TOKENS_KEY      = "num_tokens";
    static String TIMES_KEY           = "execution_times";

    static int WARMUP_RUNS            = 2;
    static int NUM_TRIALS             = 5;

    // Utility methods

    public static CommonTokenStream getTokenStream(Benchmark benchmark, String dataFile) throws IOException {
	CharStream stream = CharStreams.fromFileName(dataFile);
	Lexer lexer;
	switch (benchmark) {
	  case JSON :
	      lexer = new JSONLexer(stream);
	      break;
	  case XML :
	      lexer = new XMLLexer(stream);
	      break;
  	  case DOT :
	      lexer = new DOTLexer(stream);
	      break;
	  case PYTHON :
	      lexer = new Python3Lexer(stream);
	      break;
	  default :
	      throw new RuntimeException("unrecognized benchmark value");
	}
	return new CommonTokenStream(lexer);
    }

    public static ParserInterpreter getInterp(Benchmark benchmark, CommonTokenStream tokens) throws IOException {
	Grammar g;
	switch (benchmark) {
	  case JSON :
	      g = Grammar.load(JSON_GRAMMAR);
	      break;
	  case XML :
	      g = Grammar.load(XML_PARSER_GRAMMAR);
	      break;
  	  case DOT :
	      g = Grammar.load(DOT_GRAMMAR);
	      break;
	  case PYTHON :
	      g = Grammar.load(PYTHON_GRAMMAR);
	      break;
	  default :
	      throw new RuntimeException("unrecognized benchmark value");
	}
	return g.createParserInterpreter(tokens);
    }

    public static String getStartSymbol(Benchmark benchmark) {
	switch (benchmark) {
	  case JSON :
	      return JSON_START_SYM;
	  case XML :
	      return XML_START_SYM;
  	  case DOT :
	      return DOT_START_SYM;
	  case PYTHON :
	      return PYTHON_START_SYM;
	  default :
	      throw new RuntimeException("unrecognized benchmark value");
	}
    }

    public static int getNumTokens(Benchmark benchmark, String dataFile) throws IOException {
	CommonTokenStream tokenStream = getTokenStream(benchmark, dataFile);
	tokenStream.fill();	
	return tokenStream.getTokens().size();
    }

    /* Methods for benchmarking ANTLR lexers and parser interpreters
       using our default experimental setup (five trials per file,
       instantiate a new lexer/parser at the beginning of each trial) */
    
    public static JSONArray runTrials(Benchmark benchmark,
				      ANTLRComponent component,
				      String dataFile) throws IOException {
	List<Double> times = new ArrayList<Double>();
	for (int i = 0; i < NUM_TRIALS; i++) {
	    CommonTokenStream tokens = getTokenStream(benchmark, dataFile);
	    long start, stop;
	    switch (component) {
	      case LEXER : // benchmark the lexer
		  start = System.nanoTime();
		  tokens.fill();
		  stop = System.nanoTime();
		  break;
	      case PARSER : // benchmark the parser
		  tokens.fill();
		  ParserInterpreter parser = getInterp(benchmark, tokens);
		  parser.setErrorHandler(new BailErrorStrategy());
		  String startSymbol = getStartSymbol(benchmark);
		  start = System.nanoTime();
		  ParseTree t = parser.parse(parser.getRuleIndex(startSymbol));
		  stop = System.nanoTime();
		  break;
	      default :
		  throw new RuntimeException("invalid ANTLRComponent option");
	    }
	    times.add((stop - start) / 1_000_000_000.0); // convert to seconds
	}
	return new JSONArray(times);
    }

    public static JSONObject benchmarkANTLRComponentOnFile(Benchmark benchmark,
							   ANTLRComponent component,
							   String dataDir,
							   String dataFileName) throws IOException {
	String dataFile = dataDir + "/" + dataFileName;
	int numTokens   = getNumTokens(benchmark, dataFile);
	JSONArray times = runTrials(benchmark, component, dataFile);
	return new JSONObject().put(FILENAME_KEY, dataFileName)
	                       .put(NUM_TOKENS_KEY, numTokens)
	                       .put(TIMES_KEY, times);
    }
    
    public static JSONArray benchmarkANTLRComponentOnDataSet(Benchmark benchmark,
							     ANTLRComponent component,
							     String dataDirName) throws IOException {
	List<JSONObject> records = new ArrayList<JSONObject>();
	String[] dataFileNames   = (new File(dataDirName)).list();
	for (int i = 0; i < dataFileNames.length; i++) {
	    System.out.println("file #" + (i + 1) + " of " + dataFileNames.length);
	    JSONObject record = benchmarkANTLRComponentOnFile(benchmark, component, dataDirName, dataFileNames[i]);
	    System.out.println(record.toString(4));
	    records.add(record);
	}
	// Sort the records by number of tokens
	records.sort((r1, r2) ->
		     Integer.valueOf(r1.getInt(NUM_TOKENS_KEY)).compareTo(Integer.valueOf(r2.getInt(NUM_TOKENS_KEY))));
	return new JSONArray(records);
    }

    /*    public static double benchmarkANTLRComponentOnFile2(ParserInterpreter parser,
							String startSymbol) throws IOException {
	long start, stop;
	int startRuleIndex = parser.getRuleIndex(startSymbol);
	start = System.nanoTime();
	ParseTree t = parser.parse(startRuleIndex);
	stop = System.nanoTime();
	return (stop - start) / 1_000_000_000.0; // convert to seconds
    }

    public static JSONArray benchmarkANTLRComponentOnCorpus(Benchmark benchmark,
							    ANTLRComponent component,
							    String dataDirName) throws IOException {
	// corpus information 
	File dataDir               = new File(dataDirName);
	List<String> dataFileNames = new ArrayList<String>(Arrays.asList(dataDir.list()));
	int totalFiles             = dataFileNames.size();

	// maps to hold the parse times and number of tokens for each file
	Map<String, List<Double>>  fileNameToTimes = new HashMap<String, List<Double>>();
	Map<String, Integer>  fileNameToNumTokens  = new HashMap<String, Integer>();


	CommonTokenStream dummyTokens = getTokenStream(benchmark, dataDirName + "/" + dataFileNames.get(0));
	ParserInterpreter parser = getInterp(benchmark, dummyTokens);
	parser.setErrorHandler(new BailErrorStrategy());
	String startSymbol = getStartSymbol(benchmark);

	for (int i = 0; i < (THROWAWAY_TRIALS + RECORDED_TRIALS); i++) {
	    System.out.println("CORPUS PASS " + (i + 1));
	    int currFileNumber = 1;
	    for (String dataFileName : dataFileNames) {
		System.out.println(dataFileName + "  (file #" + currFileNumber + " of " + totalFiles + ")");
		currFileNumber++;
		String dataFile = dataDirName + "/" + dataFileName;
		fileNameToNumTokens.put(dataFileName, getNumTokens(benchmark, dataFile));

		CommonTokenStream tokens = getTokenStream(benchmark, dataFile);
		tokens.fill();
		parser.setTokenStream(tokens);
		
		double time = benchmarkANTLRComponentOnFile2(parser, startSymbol);
		if (i >= THROWAWAY_TRIALS) {
		    if (fileNameToTimes.containsKey(dataFileName)) {
			List<Double> prevTimes = fileNameToTimes.get(dataFileName);
			prevTimes.add(time);
		    } else {
			List<Double> times = new ArrayList<Double>();
			times.add(time);
			fileNameToTimes.put(dataFileName, times);
		    }
		}
		parser.reset();
	    }
	}
	List<JSONObject> records = new ArrayList<JSONObject>();
        fileNameToTimes.forEach((fname, times) ->
				records.add(new JSONObject().put(FILENAME_KEY, fname)
					                    .put(NUM_TOKENS_KEY, fileNameToNumTokens.get(fname))
                       					    .put(getTimesKey(component), times)));
	// Sort the records by number of tokens
	records.sort((r1, r2) ->
		     Integer.valueOf(r1.getInt(NUM_TOKENS_KEY)).compareTo(Integer.valueOf(r2.getInt(NUM_TOKENS_KEY))));
	return new JSONArray(records);
    }
    */
    
    public static void writeResults(JSONArray benchmarkResults, String outFileName) throws Exception {
	PrintWriter writer = new PrintWriter(outFileName, "UTF-8");
	writer.print(benchmarkResults.toString(4));
	writer.close();
    }

    public static void main(String[] args) throws Exception {

	String benchmarkName = args[0];
	String componentName = args[1];
	String dataDirName   = args[2];
	String outFileName   = args[3];

	Benchmark benchmark;
	switch (benchmarkName) {
	  case "json" :
	      benchmark = Benchmark.JSON;
	      break;
	  case "xml" :
	      benchmark = Benchmark.XML;
	      break;
	  case "dot" :
	      benchmark = Benchmark.DOT;
	      break;
	  case "python" :
	      benchmark = Benchmark.PYTHON;
	      break;
	  default:
	      throw new RuntimeException("invalid benchmark name");
	}

	ANTLRComponent component;
	switch (componentName) {
	  case "lexer" :
	      component = ANTLRComponent.LEXER;
	      break;
	  case "parser" :
	      component = ANTLRComponent.PARSER;
	      break;
	  default:
	      throw new RuntimeException("invalid component name");
	}

	for (int i = 0; i < WARMUP_RUNS; i++) {
	    System.out.println("*** WARM-UP RUN #" + (i + 1) + " ***");
	    JSONArray records = benchmarkANTLRComponentOnDataSet(benchmark, component, dataDirName);
	}
	System.out.println("*** TEST RUN ***");
	JSONArray records = benchmarkANTLRComponentOnDataSet(benchmark, component, dataDirName);
	writeResults(records, outFileName);
    }
}
