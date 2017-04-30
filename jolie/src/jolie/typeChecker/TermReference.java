package jolie.typeChecker;

public class TermReference {
    private String id;
    private TermType type;

    TermReference(String id, TermType type) {
        this.id = id;
        this.type = type;
    }

    public String id() {
        return id;
    }

    public TermType type() {
        return type;
    }
}
