package othello.client;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class OthelloClient implements Client, Runnable {

    private Socket socket;
    private Thread thread;
    private List<Listener> listeners = new ArrayList<>();
    private BufferedWriter bw;

    public boolean connect(InetAddress address, int port) {
        try {
            socket = new Socket(address, port);
            bw = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            thread = new Thread(this);
            thread.start();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    public void close() {
        try {
            socket.close();
            //thread.join(); // maybe not
        } catch (IOException | /*InterruptedException | */ NullPointerException e) {
            throw new RuntimeException(e);
        }
    }

    public boolean sendUsername(String username) {
        try {
            bw.write(Protocol.printMessage(username));
            bw.newLine();
            bw.flush();
            //sendMessage("connected");
            return true;
        } catch (IOException | NullPointerException e) {
            close();
            return false;
        }
    }

    public boolean sendMessage(String message) {
        try {
            bw.write(Protocol.printMessage(message));
            bw.newLine();
            bw.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }
    }

    public boolean getLoggedIn() {
        return hasLoggedIn;
    }

    public void setPlayer(Player player) {
        this.player = player;
    }
}
