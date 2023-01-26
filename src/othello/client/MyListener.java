package othello.client;

public class MyListener implements Listener {
    public void messageReceived(String from, String msg) {
        System.out.printf("<%s> %s\n", from, msg);
    }
}
