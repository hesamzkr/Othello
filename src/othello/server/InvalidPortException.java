package othello.server;

public class InvalidPortException extends Exception {

    private final String msg;

    public InvalidPortException(String msg) {
        this.msg = msg;
    }

    @Override
    public String getMessage() {
        return msg;
    }
}
