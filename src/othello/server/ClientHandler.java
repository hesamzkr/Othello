package othello.server;

import othello.client.Protocol;
import othello.game.NoValidMoves;
import othello.game.OthelloGame;

import java.io.*;
import java.net.Socket;

public class ClientHandler implements Runnable {
    private final Socket socket;
    private final OthelloServer server;
    private String username;
    private final BufferedWriter bw;
    private ClientHandler opponent;
    private OthelloGame game;


    public ClientHandler(Socket socket, OthelloServer server) throws IOException {
        this.socket = socket;
        this.server = server;
        bw = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
        new Thread(this).start();
    }

    public void run() {
        try (BufferedReader br = new BufferedReader(new InputStreamReader(socket.getInputStream()))) {
            while (!socket.isClosed()) {
                String line;
                while ((line = br.readLine()) != null) {
                    String[] protocolSplit = line.split(Protocol.SEPARATOR);
                    switch (protocolSplit[0]) {
                        case Protocol.HELLO -> {
                            if (protocolSplit.length > 1) {
                                send(Protocol.sendHelloServer());
                            } else {
                                sendError("No description");
                            }
                        }
                        case Protocol.LOGIN -> {
                            if (protocolSplit.length > 1) {
                                if (server.usernameExists(protocolSplit[1])) {
                                    send(Protocol.ALREADYLOGGEDIN);
                                } else {
                                    username = protocolSplit[1];
                                    send(Protocol.LOGIN);
                                }
                            } else {
                                sendError("No username");
                            }
                        }
                        case Protocol.LIST -> send(Protocol.sendList(server.getUsernames()));
                        case Protocol.QUEUE -> server.handleQueue(this);
                        case Protocol.MOVE -> {
                            if (protocolSplit.length > 1) {
                                int moveIndex = Integer.parseInt(protocolSplit[1]);
                                if (game.isValidMove(moveIndex)) {
                                    try {
                                        game.doMove(moveIndex);
                                        opponent.sendOpponentsMove(moveIndex);
                                    } catch (NoValidMoves ignored) {
                                        opponent.sendOpponentsMove(64);
                                    }
                                    game.nextTurn();
                                }
                            } else {
                                sendError("No move index");
                            }
                        }
                    }
                }
            }
        } catch (IOException e) {
            close();
        }
    }

    /**
     * Send the move the opponent made to the client
     *
     * @param moveIndex
     */
    public void sendOpponentsMove(int moveIndex) {
        send(Protocol.sendMove(moveIndex));
    }

    public void sendError(String msg) {
        send(Protocol.sendError(msg));
    }

    public void sendNewGame(String p1, String p2) {
        send(Protocol.sendNewGame(p1, p2));
    }

    /**
     * Send the message to the client
     *
     * @param msg the message
     */
    public void send(String msg) {
        try {
            bw.write(msg);
            bw.newLine();
            bw.flush();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public void close() {
        try {
            server.removeClient(this);
            socket.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public String getUsername() {
        return username;
    }

    public ClientHandler getOpponent() {
        return opponent;
    }

    public void setOpponent(ClientHandler opponent) {
        this.opponent = opponent;
    }

    public void setGame(OthelloGame game) {
        this.game = game;
    }
}
