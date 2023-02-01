package othello.server;

import othello.client.Protocol;
import othello.game.NoValidMoves;
import othello.game.OthelloGame;

import java.io.*;
import java.net.Socket;

/**
 * Handler class for each client and their connection to the server
 * Running on a separate reads the client's messages using sockets
 */
public class ClientHandler implements Runnable {
    private final Socket socket;
    private final OthelloServer server;
    private String username;
    private final BufferedWriter bw;
    private ClientHandler opponent;
    private OthelloGame game;
    private boolean hasGreeted = false;
    private boolean hasLoggedIn = false;


    /**
     * Constructor that sets the socket, server, and writers. It starts a separate thread to read clients messages
     *
     * @param socket connected to the server
     * @param server which it is connected to
     * @throws IOException if output stream of socket is unavailable
     */
    public ClientHandler(Socket socket, OthelloServer server) throws IOException {
        this.socket = socket;
        this.server = server;
        bw = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
        new Thread(this).start();
    }

    /**
     * As long as socket isn't closed read from the sockets stream and process clients messages
     */
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
                                        } catch (NoValidMoves ignored) {
                                        }
                                        game.nextTurn();
                                        send(Protocol.sendMove(moveIndex));
                                        /*
                                        need to make sure the move is sent to this client first if there's a gameOver
                                        condition as otherwise sometimes opponent.send(Move) is sent after the gameOver
                                        */
                                        Thread.sleep(100);
                                        opponent.send(Protocol.sendMove(moveIndex));

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
                                } catch (InterruptedException e) {
                                    throw new RuntimeException(e);
                                } catch (NullPointerException ignored) {
                                    // needed as game or opponent can be null if a disconnect happens due to reset()
                                }
                            } else {
                                sendError("No move index");
                            }
                        }
                        default -> sendError(line);
                    }
                }
            }
        } catch (IOException e) {
            close();
        }
    }

    /**
     * Sends error message to client using Protocol
     *
     * @param msg error message
     */
    public void sendError(String msg) {
        send(Protocol.sendError(msg));
    }

    /**
     * Send new game message with player names
     *
     * @param p1 player1 username
     * @param p2 player2 username
     */
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

    /**
     * Close the socket and remove from the list of clients.
     * If user was in a game make the opponent win and send the disconnect message
     */
    public void close() {
        try {
            if (game != null && !opponent.socket.isClosed()) {
                opponent.reset();
                opponent.send(Protocol.sendWinDisconnect(opponent.getUsername()));
            }
            server.removeClient(this);
            socket.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Returns the clients username
     *
     * @return username
     */
    public String getUsername() {
        return username;
    }

    /**
     * Set opponent as a clientHandler when a game is found to send messages to opponent client
     *
     * @param opponent the opponent clientHandler
     */
    public void setOpponent(ClientHandler opponent) {
        this.opponent = opponent;
    }

    /**
     * Set new game shared between both clientHandlers
     *
     * @param game the game
     */
    public void setGame(OthelloGame game) {
        this.game = game;
    }

    /**
     * Set game and opponent to null when client is no longer in a game
     */
    public void reset() {
        opponent = null;
        game = null;
    }
}
