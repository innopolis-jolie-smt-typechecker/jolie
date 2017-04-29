package jolie.typeChecker;

import java.util.HashSet;

public class StatementsContext {
    private StatementsContext parent;
    private StatementsContext child;

    private HashSet<String> declaredConsts;

    StatementsContext() {
        this(null);
    }

    private StatementsContext(StatementsContext parent) {
        this.declaredConsts = new HashSet<>();

        if (parent != null) {
            this.parent = parent;
        }
    }

    public StatementsContext push() {
        this.child = new StatementsContext(this);
        return this.child;
    }

    public StatementsContext pop() throws Exception {
        if (this.parent != null) {
            this.parent.child = null;
            return this.parent;
        } else {
            throw new Exception("Can't pop from the top level context");
        }
    }

    public boolean add(String item) {
        return declaredConsts.add(item);
    }

    public boolean contains(String item) {
        boolean parentContains = false;
        if (parent != null) parentContains = parent.contains(item);
        return parentContains || declaredConsts.contains(item);
    }
}
