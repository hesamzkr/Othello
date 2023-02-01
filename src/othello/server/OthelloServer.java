package othello.server;

import othello.game.HumanPlayer;
import othello.game.OthelloGame;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * A Runnable Server specialised for queuing and managing the othello
 * game runs on a thread and has a thread separate for matchmaking
 */
public class OthelloServer implements Server, Runnable {

    private ServerSocket serverSocket;

    private Thread connectionThread;

    private Thread matchMakingThread;

    private final List<ClientHandler> clients;

    private final Queue<ClientHandler> queue;

    private final int port;

    /**
     * Constructor which sets the port and initializes clients and queue
     *
     * @param port the server's port
     */
    public OthelloServer(int port) {
        this.port = port;
        clients = new ArrayList<>();
        queue = new LinkedList<>();
    }

    /**
     * Starts the server by having itself run on a separate thread which accepts connections
     * and create a matchmaking thread which queues two clientHandlers if possible.
     */
    public void start() {
        try {
            serverSocket = new ServerSocket(port);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        connectionThread = new Thread(this);
        connectionThread.start();
        matchMakingThread = new Thread(() -> {
            while (!serverSocket.isClosed()) {
                synchronized (queue) {
                    if (queue.size() >= 2) {
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

    /**
     * Returns the port of the server. This method returns the actual port the server is accepting connections on.
     *
     * @return the port number, between 0 and 65535.
     */
    public int getPort() {
        return port;
    }

    /**
     * Returns the size of the queue of othello clientHandlers
     *
     * @return the size of the queue
     */
    public int getQueueSize() {
        return queue.size();
    }

    /**
     * Stops the server. This method returns after the server
     * connection thread and matchmaking thread has actually stopped.
     */
    public void stop() {
        try {
            for (ClientHandler client : clients) {
                client.close();
            }
            serverSocket.close();
            connectionThread.join();
            matchMakingThread.join();
            System.out.println("Server closed");
        } catch (IOException | InterruptedException ignored) {
        }
    }

    /**
     * Returns true if the server is currently accepting connections, and false otherwise.
     *
     * @return if the server is accepting connections
     */
    public boolean isAccepting() {
        return connectionThread != null && connectionThread.isAlive();
    }

    /**
     * Checks if a ClientHandler is already queued and if so removes them, otherwise adds them to the queue.
     *
     * @param from ClientHandler to be checked
     */
    public void handleQueue(ClientHandler from) {
        // must be synchronized as the matchmaking thread is also accessing and changing the queue
        synchronized (queue) {
            if (queue.contains(from)) {
                queue.remove(from);
            } else {
                queue.add(from);
            }
        }
    }

    /**
     * For the connectionThread to accept new connections as long as the thread is alive
     */
    @Override
    public void run() {
        try {
            while (isAccepting()) {
                Socket socket = serverSocket.accept();
                System.out.printf("Connection from %s%n", socket.getInetAddress().getHostAddress());
                ClientHandler handler = new ClientHandler(socket, this);
                addClient(handler);
            }
        } catch (IOException e) {
            System.out.println("Socket closed");
        }
    }

    /**
     * Add the client to the list of clients
     *
     * @param client to be added
     */
    public void addClient(ClientHandler client) {
        clients.add(client);
    }

    /**
     * Remove client from the list of clients
     *
     * @param client to be removed
     */
    public void removeClient(ClientHandler client) {
        clients.remove(client);
    }

    /**
     * Returns the IP address of the server
     *
     * @return server's IP address
     */
    public String getAddress() {
        return serverSocket.getInetAddress().getHostAddress();
    }

    /**
     * Checks if a client with this username is already logged into the server
     *
     * @param username to be checked
     * @return whether the username has been logged in
     */
    public boolean usernameExists(String username) {
        return getUsernames().contains(username);
    }

    /**
     * Compiles a list of clients usernames
     *
     * @return list of clients usernames
     */
    public List<String> getUsernames() {
        return clients.stream().map(ClientHandler::getUsername).filter(Objects::nonNull).collect(Collectors.toList());
    }
}
