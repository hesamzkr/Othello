package othello.client;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class MyClient implements Client, Runnable {

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

    public void addChatListener(Listener listener) {
        listeners.add(listener);
    }

    public void removeChatListener(Listener listener) {
        listeners.remove(listener);
    }

    public void run() {
        try (BufferedReader br = new BufferedReader(new InputStreamReader(socket.getInputStream()))) {
            while (!socket.isClosed()) {
                String line;

                while ((line = br.readLine()) != null) {
                    String[] protocolSplit = line.split(Protocol.SEPARATOR);
                    String from = protocolSplit[2];
                    String message = protocolSplit[3];
                    for (Listener listener : listeners) {
                        listener.messageReceived(from, message);
                    }
                }
            }
        } catch (IOException e) {
//            for (ChatListener listener: listeners) {
//                listener.messageReceived("server", "message");
//            }
            close();
        }
    }
}
