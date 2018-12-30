/*
 * This file is part of alloy2smt.
 * Copyright (C) 2018-2019  The University of Iowa
 * 
 * @author Mudathir Mohamed, Paul Meng
 *
 */

package edu.uiowa.alloy2smt;
import java.io.BufferedReader;
import org.apache.commons.cli.*;

import java.util.*;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.InvalidPathException;
import java.nio.file.Paths;
import java.util.concurrent.TimeUnit;

public class Main
{
    public static final String OS                   = System.getProperty("os.name");
    public static final String SEP                  = File.separator;
    public static final String OUTPUT_DIR           = System.getProperty("java.io.tmpdir");
    public static final String BIN_PATH             = System.getProperty("user.dir")+SEP+"bin"+SEP;
    public static final String DEFAULT_OUTPUT_FILE  = "output.smt2";

    public static boolean isValidInputFilePath(String path)
    {
        File inputFile = new File(path);
        
        return inputFile.exists() && inputFile.canRead() && path.endsWith(".als");
    }
    
    public static boolean isValidOutputFilePath(String path) throws IOException
    {
        try 
        {
            Paths.get(path);          
        } 
        catch (InvalidPathException | NullPointerException ex) 
        {
            return false;
        }
        
        File outputFile = new File(path);
        
        if (outputFile.getParentFile() != null) 
        {
          outputFile.getParentFile().mkdirs();
        }
        outputFile.createNewFile();          
        return true;        
    } 
    
    public static boolean isNumeric(String str)
    {
      return str.matches("\\d+(\\.\\d+)?");  
    }    
    
    public static void executeCVC4(String cvc4, String fileName, String[] cvc4Flags, String timeout) throws InterruptedException
    {
        if(cvc4 == null) 
        {
            if(OS.startsWith("Windows"))
            {
                cvc4 = BIN_PATH + "cvc4_win64.exe";
            }
            else if(OS.startsWith("Linux"))
            {
                cvc4 = BIN_PATH + "cvc4_linux";
            }
            else 
            {
                System.out.println("No CVC4 binary available for the OS: " + OS);
                return;
            }
            
        }        
        if(fileName == null) 
        {
            System.out.println("No input file for CVC4!");
            return;
        }        
        
        File cvc4Binary = new File(cvc4);
        
        if(!cvc4Binary.exists())
        {
            System.out.println("CVC4 binary does not exist at: " + cvc4);
            return;
        }
        if(!cvc4Binary.canExecute())
        {
            System.out.println("CVC4 binary cannot be executed at: " + cvc4);
            return;            
        }
        
        ProcessBuilder  pb          = new ProcessBuilder();
        List<String>    commands    = new ArrayList<>();
        
        commands.add(cvc4);
        commands.add(fileName);
        
        if(cvc4Flags != null)
        {
            commands.addAll(Arrays.asList(cvc4Flags));               
        } 
        
        double timeoutSecs = 300;
        
        if(timeout != null && isNumeric(timeout))
        {
            timeoutSecs = Double.parseDouble(timeout);
        }
                
        try 
        {
            pb.command(commands); 
            System.out.println("**************************************** Checking with CVC4 ****************************************");            
            System.out.println("\nCommand executed: " + pb.command());
            Process process = pb.start();
            if(process.waitFor((long) timeoutSecs, TimeUnit.SECONDS))
            {
                System.out.println("CVC4 Output: " + output(process.getInputStream()));
            }
            else
            {
                System.out.println("Timeout: " + timeoutSecs + " seconds");
            }
            System.out.println("********************************************************************************************************\n");                          
            process.destroy();
        } 
        catch (IOException ex) {            
        }         
    }    
    
    private static String output(InputStream inputStream) throws IOException 
    {
        StringBuilder   sb = new StringBuilder();
        BufferedReader  br = null;
        try
        {
            br = new BufferedReader(new InputStreamReader(inputStream));
            String line = br.readLine();
            String fstLine = line;
            while (line != null) 
            {
                if(fstLine.equalsIgnoreCase("sat") || fstLine.equalsIgnoreCase("unknown"))
                {
                    sb.append(line).append(System.getProperty("line.separator"));
                }
                else
                {
                    sb.append(line).append(System.getProperty("line.separator"));
                    break;
                }
                line = br.readLine();
            }
        } 
        finally 
        {
            br.close();
        }
        return sb.toString();
    }     
    
    public static void main(String[] args)
    {
        Options             options             = new Options();
        CommandLineParser   commandLineParser   = new DefaultParser();        
        
        options.addOption(Option.builder("i").longOpt("input").desc("Input Alloy model").hasArg().build());
        options.addOption(Option.builder("o").longOpt("output").desc("SMT-LIB model output").hasArg().build());
        options.addOption(Option.builder("b").longOpt("cvc4-binary").desc("CVC4 binary path").hasArg().build());
        options.addOption(Option.builder("f").longOpt("cvc4-flags").desc("Additional CVC4 flags").hasArgs().build());
        options.addOption(Option.builder("c").longOpt("command").desc("An integer that specifies the index of the command to be translated").hasArg().build());
        options.addOption(Option.builder("t").longOpt("timeout").desc("Timeout(s)").hasArg().build());
        
        try
        {
            CommandLine command = commandLineParser.parse(options, args);

            String  cvc4Binary      = command.hasOption("b")?command.getOptionValue("b").trim():null;
            int     assertion       = command.hasOption("c")?Integer.parseInt(command.getOptionValue("c").trim()):0;
            String  timeout         = command.hasOption("t")?command.getOptionValue("t").trim():null;

            String output;
            String defaultOutputFile;

            if (command.hasOption("i"))
            {
                String inputFile = command.getOptionValue("i").trim();

                if (isValidInputFilePath(inputFile))
                {
                    File alloyFile    = new File(inputFile);
                    output            = Utils.translateFromFile(alloyFile.getAbsolutePath(), assertion);
                    defaultOutputFile = OUTPUT_DIR + SEP + alloyFile.getName() + ".smt2";
                } else
                {
                    throw new Exception("Can not open file " + inputFile);
                }
            }
            else
            {
                StringBuilder stringBuilder = new StringBuilder();
                Scanner scanner             = new Scanner(System.in);

                while(scanner.hasNextLine())
                {
                    stringBuilder.append(scanner.nextLine()).append("\n");
                }

                output              = Utils.translateFromString(stringBuilder.toString(), assertion);
                defaultOutputFile   = DEFAULT_OUTPUT_FILE + ".smt2";
            }

            File outputFile = null;
                    
            if(command.hasOption("o"))
            {
                if(isValidOutputFilePath(command.getOptionValue("o")))
                {
                    outputFile = new File(command.getOptionValue("o").trim());
                }
            }
            if(outputFile == null)
            {
                outputFile = new File(defaultOutputFile);
            }
            try (Formatter formatter = new Formatter(outputFile))
            {
                formatter.format("%s", output);
            }

            // Execute CVC4 on the output file
            executeCVC4(cvc4Binary, outputFile.getAbsolutePath(), command.hasOption("f")?command.getOptionValues('f'):null, timeout);
            System.out.println("\n");
            System.out.println(output);
            System.out.println("\nThe SMT-LIB model was generated at: " + outputFile.getAbsolutePath());
        }
        catch (ParseException exception)
        {
            HelpFormatter formatter = new HelpFormatter();
            formatter.printHelp( "java -jar alloy2smt.jar ", options );
        }
        catch (Exception exception)
        {
            exception.printStackTrace();
        }
    }
}
