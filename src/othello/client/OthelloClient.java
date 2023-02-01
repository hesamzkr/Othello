package othello.client;

import othello.game.*;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.List;

/**
 * Client which handles connection to the server and reading the server's messages and handling them.
 * Handling game and players to as both Human an AI can use this client.
 */
public class OthelloClient implements Client, Runnable {

    private Socket socket;
    private final OthelloListener listener = new OthelloListener(this);
    private BufferedWriter bw;
    private String username;
    private Player player;
    private OthelloGame game;
    private boolean hasLoggedIn = false;

    /**
     * When boolean field is set to true the readers of user input in TUI take nothing as a value, and pass it on.
     * In other words they ignore the user input. This is used when the TUI thread is waiting for user input
     * but the current menu is no longer valid and by pressing enter the new menu is presented to the user.
     */
    public volatile boolean pressEnter = false;

    /**
     * Create a socket connection to the server with given IP address and port.
     * Then run the client on a separate thread to read and handle the server's messages.
     *
     * @param address IP address of the server
     * @param port    server's port
     */
    public void connect(InetAddress address, int port) {
        try {
            socket = new Socket(address, port);
            bw = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            Thread thread = new Thread(this);
            thread.start();
        } catch (IOException ignored) {
        }
    }

    /**
     * As long as socket isn't closed read from the sockets input stream and process server's messages.
     */
    public void run() {
        try (BufferedReader br = new BufferedReader(new InputStreamReader(socket.getInputStream()))) {
            while (!socket.isClosed()) {
                String line;
                while ((line = br.readLine()) != null) {
                    String[] protocolSplit = line.split(Protocol.SEPARATOR);
                    switch (protocolSplit[0]) {
                        case Protocol.HELLO -> listener.printHello(protocolSplit[1]);
                        case Protocol.LOGIN -> hasLoggedIn = true;

                        case Protocol.LIST -> listener.printList(protocolSplit);

                        case Protocol.NEWGAME -> {
                            if (protocolSplit[1].equals(player.getName())) {
                                game = new OthelloGame(player, new HumanPlayer(protocolSplit[2]));
                                listener.printNewGameFound(protocolSplit[2], Mark.BLACK);
                            } else {
                                game = new OthelloGame(new HumanPlayer(protocolSplit[1]), player);
                                listener.printNewGameFound(protocolSplit[1], Mark.WHITE);
                            }
                        }
                        case Protocol.MOVE -> {
                            try {
                                while (pressEnter) {
                                    Thread.onSpinWait();
                                }
                                if (game == null) {
                                    continue;
                                }
                                int moveIndex = Integer.parseInt(protocolSplit[1]);
                                if (moveIndex == 64) {
                                    if (game.getTurn() != player) {
                                        listener.printOpponentSkipped();
                                    }
                                } else {
                                    game.doMove(moveIndex);
                                }
                                game.nextTurn();
                                listener.printGame();
                                if (game.getTurn() == player) {
                                    printMoves();
                                    if (player instanceof ComputerPlayer) {
                                        sendAIMove();
                                    }
                                } else {
                                    listener.print("Waiting for the opponent");
                                }

                            } catch (NoValidMovesException ignored) {
                            }
                        }
                        case Protocol.GAMEOVER -> {
                            switch (protocolSplit[1]) {
                                case Protocol.DRAW -> listener.printGameOverDraw();
                                case Protocol.DISCONNECT -> listener.printGameOverDisconnected(protocolSplit[2]);
                                case Protocol.VICTORY -> listener.printGameOverVictory(protocolSplit[2]);
                            }
                            pressEnter = true;
                            game = null;
                            player = null;
                        }
                        case Protocol.ERROR -> System.out.println(line);
                    }
                }
            }
        } catch (IOException e) {
            close();
        }
    }

    /**
     * closes the socket
     */
    public void close() {
        try {
            socket.close();
            System.out.println("Closing client");
            System.exit(0);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Send the message to the server
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
     * If game isn't over send the move to server using Protocol.
     *
     * @param moveIndex the move's index
     */
    public void sendMove(int moveIndex) {
        if (game.isGameOver()) {
            return;
        }
        send(Protocol.sendMove(moveIndex));
    }

    /**
     * Should only be called if the player is a ComputerPlayer.
     * Player determines the move depending on its strategy and sends the move to server
     */
    public void sendAIMove() {
        try {
            if (game.isGameOver()) {
                return;
            }
            List<Move> moves = player.determineMove(game);
            int aiMoveIndex = moves.get(0).getIndex();
            sendMove(aiMoveIndex);
        } catch (NoValidMovesException ignored) {
            sendMove(64);
        }

    }

    /**
     * Calls the listener print moves to output the valid moves to the UI
     */
    public void printMoves() {
        listener.printMoves();
    }

    /**
     * Returns if the client is logged in on the server
     *
     * @return whether client is logged in
     */
    public boolean getLoggedIn() {
        return hasLoggedIn;
    }

    /**
     * Returns the player chosen to play the game
     *
     * @return the player playing the game
     */
    public Player getPlayer() {
        return player;
    }

    /**
     * Sets the player to play the game. This could be both a ComputerPlayer or a HumanPlayer
     *
     * @param player to play the game
     */
    public void setPlayer(Player player) {
        this.player = player;
    }

    /**
     * Return the username of the client
     *
     * @return client's username
     */
    public String getUsername() {
        return username;
    }

    /**
     * Sets the username that the server must validate to be available
     */
    public void setUsername(String username) {
        this.username = username;
    }

    /**
     * Returns the current game client is playing
     *
     * @return the game
     */
    public OthelloGame getGame() {
        return game;
    }
}
