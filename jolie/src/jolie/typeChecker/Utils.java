package jolie.typeChecker;

public class Utils {
    private static Integer nextConstId = 0;
    private static final String termPrefix = "$$__term_id_";

    public static String getNextTermId() {
        String id = termPrefix + nextConstId.toString();
        nextConstId++;
        return id;
    }
}
