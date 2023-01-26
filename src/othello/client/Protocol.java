package othello.client;

import java.util.List;

/**
 * Protocol class with constants and methods for creating protocol messages
 */
public final class Protocol {
    public static final String SEPARATOR = "~";
    public static final String ERROR = "ERROR";

    public static final String HELLO = "HELLO";
    public static final String LOGIN = "LOGIN";

    public static final String ALREADYLOGGEDIN = "ALREADYLOGGENIN";
    public static final String LIST = "LIST";

    public static final String QUEUE = "QUEUE";
    public static final String NEWGAME = "NEWGAME";

    public static final String MOVE = "MOVE";
    public static final String GAMEOVER = "GAMEOVER";
    public static final String RANK = "RANK";
    public static final String CHAT = "CHAT";

    /**
     * When provided with illegal inputs, the server or client can respond with an error.
     *
     * @param message
     * @return
     */
    public static String sendError(String message) {
        return ERROR + SEPARATOR + message;
    }

    /**
     * The initial message sent by the client once a connection has been established.
     *
     * @param username
     * @return
     */
    public static String sendHelloClient(String username) {
        return HELLO + SEPARATOR + "Client" + username;
    }

    /**
     * The initial message sent by the client once a connection has been established. Includes extensions.
     * !!!!!!!!! Should a server be able to handle different clients using the game? > If there client sends chat + rank what would happen.
     *
     * @param username
     * @return
     */
    public static String sendHelloExClient(String username) {
        return HELLO + SEPARATOR + "Client" + username + CHAT + RANK;
    }

    /**
     * Response to the initial HELLO by the client.
     *
     * @return
     */
    public static String sendHelloServer() {
        return HELLO + SEPARATOR + "Server";
    }

    /**
     * Response to initial HELLO by the client.
     *
     * @return
     */
    public static String sendHelloExServer() {
        return HELLO + SEPARATOR + "Server" + CHAT + RANK;
    }

    /**
     * Sent by the client to claim a username on the server.
     *
     * @param username
     * @return
     */
    public static String sendLogin(String username) {
        return LOGIN + SEPARATOR + username;
    }

    /**
     * Sent by the server as a reply to a LIST command from a client.
     * Lists the different usernames that are currently logged into the server, including the requesting client.
     * The order of the usernames can be arbitrary.
     *
     * @param list
     * @return
     */
    public static String sendList(List<String> list) {
        StringBuilder msg = new StringBuilder(LIST);
        for (String i : list) {
            msg.append(SEPARATOR).append(i);
        }
        return msg.toString();
    }

    /**
     * Sent by the server to all players that are put into a newly-started game.
     * Only players that were queued (see QUEUE) are allowed to be put into a game. A player can only be in at most one game simultaneously.
     *
     * @param p1
     * @param p2
     * @return
     */
    public static String sendNewGame(String p1, String p2) {
        return NEWGAME + SEPARATOR + p1 + SEPARATOR + p2;
    }

    /**
     * Sent by the client to indicate which row(s) or column(s) the player wants to push.
     *
     * @param index
     * @return
     */
    public static String sendMove(int index) {
        return MOVE + SEPARATOR + index;
    }

    /**
     * Sent if the game ended with one of the players winning.
     *
     * @param username
     * @return
     */
    public static String sendWin(String username) {
        return GAMEOVER + "VICTORY" + username;
    }

    /**
     * Sent if the game ended due to losing connection to one of the players. The winner is the player with whom the connection is still alive.
     *
     * @param username
     * @return
     */
    public static String sendWinDisconnect(String username) {
        return GAMEOVER + "DISCONNECT" + username;
    }

    /**
     * Sent if the game ended in a draw.
     *
     * @return
     */
    public static String sendDraw() {
        return GAMEOVER + "DRAW";
    }
}
