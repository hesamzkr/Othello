package othello.server;

import othello.game.HumanPlayer;
import othello.game.OthelloGame;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;
import java.util.*;
import java.util.stream.Collectors;

public class OthelloServer implements Server, Runnable {

    private ServerSocket serverSocket;

    private Thread connectionThread;

    private Thread matchMakingThread;

    private final List<ClientHandler> clients;

    private final Queue<ClientHandler> queue;

    private final int port;

    public OthelloServer(int port) {
        this.port = port;
        clients = new ArrayList<>();
        queue = new LinkedList<>();
    }

    public void start() {
        try {
            serverSocket = new ServerSocket(port);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        connectionThread = new Thread(this);
        connectionThread.start();
        matchMakingThread = new Thread(() -> {
            while (true) {
                synchronized (queue) {
                    if (!queue.isEmpty() && queue.size() % 2 == 0) {
                        ClientHandler clientHandler1 = queue.remove();
                        ClientHandler clientHandler2 = queue.remove();
                        clientHandler1.setOpponent(clientHandler2);
                        clientHandler2.setOpponent(clientHandler1);
                        OthelloGame game = new OthelloGame(new HumanPlayer(clientHandler1.getUsername()), new HumanPlayer(clientHandler2.getUsername()));
                        clientHandler1.setGame(game);
                        clientHandler2.setGame(game);
                        clientHandler1.sendNewGame(clientHandler1.getUsername(), clientHandler2.getUsername());
                        clientHandler2.sendNewGame(clientHandler1.getUsername(), clientHandler2.getUsername());
                    }
                }
            }
        });
        matchMakingThread.start();
    }

    public int getPort() {
        return port;
    }

    public int getQueue() {
        return queue.size();
    }

    public void stop() {
        try {
            for (ClientHandler client : queue) {
                client.close();
            }
            serverSocket.close();
            connectionThread.join();
            matchMakingThread.interrupt();
        } catch (IOException | InterruptedException ignored) {
        }
    }

    public boolean isAccepting() {
        return connectionThread != null && connectionThread.isAlive();
    }

    public void handleQueue(ClientHandler from) {
        synchronized (queue) {
            if (queue.contains(from)) {
                queue.remove(from);
            } else {
                queue.add(from);
            }
        }
    }

    @Override
    public void run() {
        try {
            while (isAccepting()) {
                Socket socket = serverSocket.accept();
                System.out.printf("Connection from %s%n", socket.getInetAddress().getHostAddress());
                ClientHandler handler = new ClientHandler(socket, this);
                addClient(handler);
            }
        } catch (SocketException e) {
            if (serverSocket.isClosed()) {
                return;
            }
            System.out.println("Socket exception");
        } catch (IOException e) {
            System.out.println("Socket closed");
        }
    }

    public void addClient(ClientHandler client) {
        clients.add(client);
    }

    public void removeClient(ClientHandler client) {
        clients.remove(client);
    }

    public String getAddress() {
        return serverSocket.getInetAddress().getHostAddress();
    }

    public boolean usernameExists(String username) {
        return getUsernames().contains(username);
    }

    public List<String> getUsernames() {
        return clients.stream().map(ClientHandler::getUsername).filter(Objects::nonNull).collect(Collectors.toList());
    }
}
