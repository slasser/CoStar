import java.io.*;
import java.util.Map.*;

import nl.bigo.rrdantlr4.*;

public class GrammarConverter {

    public static void convert(String inPath, String outPath) throws Exception {
	DiagramGenerator gen = new DiagramGenerator(inPath);	
	PrintWriter writer = new PrintWriter(outPath, "UTF-8");
	for (Entry<String,String> e : gen.getRules().entrySet()) {
	    String lhs = e.getKey();
	    if (Character.isLowerCase(lhs.charAt(0))) {
		String dsl  = e.getValue().replace(".toString()", "");
		String line = "('" + lhs + "'," + dsl + ")";
		System.out.println(line);
		writer.println(line);
	    }
	}
	writer.close();
    }

    public static void convertAll(String inDirName, String outDirName) throws Exception {
	File outDir = new File(outDirName);
	if (!outDir.exists()) {
	    outDir.mkdir();
	}
	String[] g4Files = new File(inDirName).list();
	for (int i = 0; i < g4Files.length; i++) {
	    String inFileName  = g4Files[i];
	    String outFileName = inFileName.replace(".g4", ".py");
	    convert(inDirName + "/" + inFileName, outDirName + "/" + outFileName);
	}
    }

    public static void main(String[] args) throws Exception {
	System.out.println(args[0]);
	convertAll(args[0], args[1]);
    }
}




/*
What about invariants made them suitable?
    invariants have to hold during return, consume, and push operations--allows for good intuition about why they're preserved
most complicated part of ALL(*) is prediction--encapsulate invariant facts into single lemma about prediction
lessons to transfer to other domains

explicitly say that invariant-based approach leads to proofs where invariant matters in base case, doesn't matter in inductive case where termination argument matters (ideally at beginning of correctness section)
*/  
