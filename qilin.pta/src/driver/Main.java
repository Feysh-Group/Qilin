/* Qilin - a Java Pointer Analysis Framework
 * Copyright (C) 2021-2030 Qilin developers
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3.0 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser Public License for more details.
 *
 * You should have received a copy of the GNU General Lesser Public
 * License along with this program.  If not, see
 * <https://www.gnu.org/licenses/lgpl-3.0.en.html>.
 */

package driver;

import org.apache.commons.io.FileUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import qilin.core.PTA;
import qilin.core.PTAScene;
import qilin.pta.PTAConfig;
import qilin.util.MemoryWatcher;
import qilin.util.PTAUtils;
import qilin.util.Stopwatch;
import soot.ModulePathSourceLocator;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.options.Options;
import soot.util.Chain;

import java.io.*;
import java.util.*;
import java.util.stream.Collectors;

public class Main {
    private static final Logger logger = LoggerFactory.getLogger(Main.class);

    public static void printSootSceneInfo() {
        Chain<SootClass> appCls = PTAScene.v().getApplicationClasses();
        Chain<SootClass> libCls = PTAScene.v().getLibraryClasses();
        System.out.println("applicationClasses: " + appCls.size() + " libraryClasses: " + libCls.size());
        System.out.println("Entries " + Scene.v().getEntryPoints().size());
        if (appCls.isEmpty()) {
            throw new RuntimeException("No application classes found");
        }
    }

    public static void addAllAppMethodsToEntries() {
        LinkedList<SootMethod> entries = new LinkedList<>(Scene.v().getEntryPoints());
        for (Iterator<SootClass> it = PTAScene.v().getApplicationClasses().snapshotIterator(); it.hasNext(); ) {
            SootClass cls = it.next();
            entries.addAll(cls.getMethods());
        }
        Scene.v().setEntryPoints(entries);
    }

    public static PTA run(String[] args) {
        PTA pta;
        new PTAOption().parseCommandLine(args);
        setupSoot();
        printSootSceneInfo();
        addAllAppMethodsToEntries();
        printSootSceneInfo();
        if (PTAConfig.v().getOutConfig().dumpJimple) {
            String jimplePath = PTAConfig.v().getAppConfig().APP_PATH.replace(".jar", "");
            PTAUtils.dumpJimple(jimplePath);
            System.out.println("Jimple files have been dumped to: " + jimplePath);
        }

        pta = PTAFactory.createPTA(PTAConfig.v().getPtaConfig().ptaPattern);
        pta.run();
        return pta;
    }

    public static void mainRun(String[] args) {
        Stopwatch ptaTimer = Stopwatch.newAndStart("Main PTA (including pre-analysis)");
        long pid = ProcessHandle.current().pid();
        MemoryWatcher memoryWatcher = new MemoryWatcher(pid, "Main PTA");
        memoryWatcher.start();
        try {
            run(args);
        } finally {
            ptaTimer.stop();
            System.out.println(ptaTimer);
            memoryWatcher.stop();
            System.out.println(memoryWatcher);
        }
    }

    public static void setupSoot() {
        setSootOptions(PTAConfig.v());
        setSootClassPath(PTAConfig.v());
        PTAScene.v().addBasicClasses();
        PTAScene.v().loadNecessaryClasses();
    }

    /**
     * Set command line options for soot.
     */
    private static void setSootOptions(PTAConfig config) {
        List<String> dirs = new ArrayList<>();
        PTAConfig.ApplicationConfiguration appConfig = config.getAppConfig();
        dirs.add(appConfig.APP_PATH);
        Options.v().set_process_dir(dirs);

        if (appConfig.MAIN_CLASS == null) {
            appConfig.MAIN_CLASS = PTAUtils.findMainFromMetaInfo(appConfig.APP_PATH);
        }

        if (appConfig.MAIN_CLASS != null) {
            Options.v().set_main_class(appConfig.MAIN_CLASS);
        }

        if (appConfig.INCLUDE_ALL) {
            Options.v().set_include_all(true);
        }

        if (appConfig.INCLUDE != null) {
            Options.v().set_include(appConfig.INCLUDE);
        }

        if (appConfig.EXCLUDE != null) {
            Options.v().set_no_bodies_for_excluded(true);
            Options.v().set_exclude(appConfig.EXCLUDE);
        }

        Options.v().setPhaseOption("jb", "use-original-names:true");
        Options.v().setPhaseOption("jb", "model-lambdametafactory:false");
        Options.v().set_output_format(Options.output_format_jimple);

        if (appConfig.REFLECTION_LOG != null) {
            Options.v().setPhaseOption("cg", "reflection-log:" + appConfig.REFLECTION_LOG);
        }

        Options.v().set_keep_line_number(true);
        Options.v().set_full_resolver(true);

        // Options.v().set_src_prec(Options.src_prec_class);
        Options.v().set_src_prec(Options.src_prec_only_class);
        Options.v().set_allow_phantom_refs(true);

    }

    /**
     * Set the soot class path to point to the default class path appended with the
     * app path (the classes dir or the application jar) and jar files in the
     * library dir of the application.
     */
    private static void setSootClassPath(PTAConfig config) {
        List<String> cps = new ArrayList<>();
        PTAConfig.ApplicationConfiguration appConfig = config.getAppConfig();
        // note that the order is important!
        cps.add(appConfig.APP_PATH);
        cps.addAll(getLibJars(appConfig.LIB_PATH));
        cps.addAll(getJreJars(appConfig.JRE));
        final String classpath = String.join(File.pathSeparator, cps);
        logger.info("Setting Soot ClassPath: {}", classpath);
        System.setProperty("soot.class.path", classpath);
    }

    private static Collection<String> getJreJars(String JRE) {
        if (JRE == null) {
            return Collections.emptySet();
        }
        final String jreLibDir = JRE + File.separator + "lib";
        return FileUtils.listFiles(new File(jreLibDir), new String[]{"jar"}, false).stream().map(File::toString)
                .collect(Collectors.toList());
    }

    /**
     * Returns a collection of files, one for each of the jar files in the app's lib
     * folder
     */
    private static Collection<String> getLibJars(String LIB_PATH) {
        if (LIB_PATH == null) {
            return Collections.emptySet();
        }
        if (LIB_PATH.equals(ModulePathSourceLocator.DUMMY_CLASSPATH_JDK9_FS)) {
            return Arrays.asList(LIB_PATH);
        }
        File libFile = new File(LIB_PATH);
        if (libFile.exists()) {
            if (libFile.isDirectory()) {
                return FileUtils.listFiles(libFile, new String[]{"jar"}, true).stream().map(File::toString)
                        .collect(Collectors.toList());
            } else if (libFile.isFile()) {
                if (libFile.getName().endsWith(".jar")) {
                    return Collections.singletonList(LIB_PATH);
                }
                logger.error("Project not configured properly. Application library path {} is not a jar file.",
                        libFile);
                System.exit(1);
            }
        }
        logger.error("Project not configured properly. Application library path {} is not correct.", libFile);
        System.exit(1);
        return null;
    }

    public static void main(String[] args) {
        mainRun(args);
    }
}
