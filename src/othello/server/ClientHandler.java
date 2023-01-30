package othello.server;

import othello.client.Protocol;
import othello.game.NoValidMoves;
import othello.game.OthelloGame;
import othello.game.Player;

import java.io.*;
import java.net.Socket;

public class ClientHandler implements Runnable {
    private final Socket socket;
    private final OthelloServer server;
    private String username;
    private final BufferedWriter bw;
    private ClientHandler opponent;
    private OthelloGame game;
    private boolean hasGreeted = false;
    private boolean hasLoggedIn = false;


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
                                hasGreeted = true;
                                send(Protocol.sendHelloServer());
                            } else {
                                sendError("No description");
                            }
                        }
                        case Protocol.LOGIN -> {
                            if (!hasGreeted) {
                                sendError("Has not established a connection");
                                continue;
                            }
                            if (protocolSplit.length > 1) {
                                if (server.usernameExists(protocolSplit[1])) {
                                    send(Protocol.ALREADYLOGGEDIN);
                                } else if (protocolSplit[1].isEmpty()) {
                                    sendError("Username can't be empty");
                                } else {
                                    username = protocolSplit[1];
                                    hasLoggedIn = true;
                                    send(Protocol.LOGIN);
                                }
                            } else {
                                sendError("No username");
                            }
                        }
                        case Protocol.LIST -> {
                            if (!hasGreeted || !hasLoggedIn) {
                                sendError("Has not established a connection");
                                continue;
                            }
                            send(Protocol.sendList(server.getUsernames()));
                        }
                        case Protocol.QUEUE -> {
                            if (!hasGreeted || !hasLoggedIn) {
                                sendError("Has not established a connection");
                                continue;
                            }
                            if (game != null || opponent != null) {
                                sendError("Currently in a game");
                                continue;
                            }
                            server.handleQueue(this);
                        }
                        case Protocol.MOVE -> {
                            if (!hasGreeted || !hasLoggedIn) {
                                sendError("Has not established a connection");
                                continue;
                            }
                            if (game == null || opponent == null) {
                                sendError("Not in a game");
                                continue;
                            }
                            if (!username.equals(game.getTurn().getName())) {
                                sendError("Not your turn");
                                continue;
                            }
                            if (protocolSplit.length > 1) {
                                try {
                                    int moveIndex = Integer.parseInt(protocolSplit[1]);
                                    if (game.isValidMove(moveIndex) || moveIndex == 64) {
                                        try {
                                            game.doMove(moveIndex);
                                            game.nextTurn();
                                            send(Protocol.sendMove(moveIndex));
                                            opponent.send(Protocol.sendMove(moveIndex));
                                        } catch (NoValidMoves ignored) {
                                            game.nextTurn();
                                            send(Protocol.sendMove(64));
                                            opponent.send(Protocol.sendMove(64));
                                        }
                                        if (game.isGameOver()) {
                                            if (game.getWinner() != null) {
                                                send(Protocol.sendWin(game.getWinner().getName()));
                                                opponent.send(Protocol.sendWin(game.getWinner().getName()));
                                            } else {
                                                send(Protocol.sendDraw());
                                                opponent.send(Protocol.sendDraw());
                                            }
                                            opponent.reset();
                                            reset();
                                        }
                                    }
                                } catch (NumberFormatException ignored) {
                                    sendError("Move index is not a number");
                                }
                            } else {
                                sendError("No move index");
                            }
                        }
                        default -> sendError("Unknown command");
                    }
                }
            }
        } catch (IOException e) {
            close();
        }
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
            close();
        }
    }

    public void close() {
        try {
            if (game != null && opponent.socket.isConnected()) {
                opponent.send(Protocol.sendWinDisconnect(opponent.getUsername()));
                opponent.reset();
            }
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

    public void reset() {
        opponent = null;
        game = null;
    }
}
