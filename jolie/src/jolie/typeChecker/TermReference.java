package jolie.typeChecker;

public class TermReference {
    private String id;
    private JolieTermType type;

    TermReference(String id, JolieTermType type) {
        this.id = id;
        this.type = type;
    }

    public String id() {
        return id;
    }

    public JolieTermType type() {
        return type;
    }
}
