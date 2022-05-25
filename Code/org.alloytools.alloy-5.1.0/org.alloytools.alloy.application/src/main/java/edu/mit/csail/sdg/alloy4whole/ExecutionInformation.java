package edu.mit.csail.sdg.alloy4whole;

import java.io.Serializable;

import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;


public class ExecutionInformation implements Serializable {

    private static final long serialVersionUID = 42L;

    public CompModule         world;
    //   public A4Solution         instance;
    public Command            cmd;

    public ExecutionInformation(CompModule world, Command cmd) {
        this.world = world;
        //  this.instance = instance;
        this.cmd = cmd;
    }


}
