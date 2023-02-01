package othello.client;

import othello.ai.Difficulty;
import othello.ai.MonteCarloStrategy;
import othello.ai.NaiveStrategy;
import othello.game.*;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Scanner;

/**
 * The main TUI which handles user inputs, states of the TUI app and interacts with the client.
 */
public class OthelloApp {
    private final OthelloClient client;
    private final Scanner scanner;
    private static final String MAIN_MENU = "1) Queue\n2) List\n3) Quit";
    private static final String IN_QUEUE = "1) Cancel Queue\n2) List\n3) Quit";
    public static final String IN_GAME = "a) List\nb) Quit";
    private static final String CHOOSE_PLAYER = "1) Human\n2) Random-AI\n3) Smart-AI";
    private static final String CHOOSE_DIFFICULTY = "1) Easy\n2) Medium\n3) Hard";

    /**
     * Constructor for app which sets client and scanner
     *
     * @param client for this app to interact with the server
     */
    public OthelloApp(OthelloClient client) {
        this.client = client;
        scanner = new Scanner(System.in);
    }

    /**
     * Create instance of app and start the TUI
     *
     * @param args system args
     */
    public static void main(String[] args) {
        OthelloApp tui = new OthelloApp(new OthelloClient());
        tui.run();
    }

    /**
     * Must be run at the beginning of the TUI to connect and do initialization stages with the server.
     * starts the mainMenu right after.
     */
    private void run() {
        String username = connectClient();
        login(username);
        runMainMenu();
    }

    /**
     * Handles user inputs for server connection and asking for username.
     * won't stop until connection is happened.
     *
     * @return username given by user
     */
    private String connectClient() {
        while (true) {
            try {
                print("Enter the server's address:");
                String address = readNextLine();
                print("Enter the port to connect to:");
                int port = readNextInt();
                client.connect(InetAddress.getByName(address), port);
                print("Connected to the server");
                print("Enter your username");
                String username = readNextLine();
                client.send(Protocol.sendHelloClient(username));
                return username;
            } catch (UnknownHostException | IllegalArgumentException ignored) {
                print("Cannot connect to the server with specified port");
            }
        }
    }

    /**
     * Takes in the username and tries to log in. won't stop until successful.
     *
     * @param username given by user
     */
    private void login(String username) {
        while (true) {
            client.send(Protocol.sendLogin(username));
            try {
                Thread.sleep(1500);
            } catch (InterruptedException e) {
                print(e.getMessage());
            }

            if (client.getLoggedIn()) {
                client.setUsername(username);
                break;
            }
            print("Choose a different username");
            username = readNextLine();
        }
    }

    /**
     * Shorthand print function for formatting and cleaner code
     *
     * @param msg to be printed
     */
    private void print(String msg) {
        System.out.printf("%s%n", msg);
    }

    /**
     * Asks the user for who will be playing the game an AI or Human, and sets the chosen player on the client.
     * won't stop until a valid player is chosen.
     */
    private void queue() {
        print(CHOOSE_PLAYER);
        while (true) {
            int choice = readNextInt();
            switch (choice) {
                case 1 -> {
                    client.setPlayer(new HumanPlayer(client.getUsername()));
                    return;
                }
                case 2 -> {
                    client.setPlayer(new ComputerPlayer(client.getUsername(), new NaiveStrategy()));
                    return;
                }
                case 3 -> {
                    client.setPlayer(new ComputerPlayer(client.getUsername(), new MonteCarloStrategy(runDifficultyMenu())));
                    return;
                }
                case 4 -> list();
                case 5 -> quit();
            }
        }
    }

    /**
     * Quits the application entirely
     */
    private void quit() {
        print("Exiting the Othello client. thank you for playing :)");
        System.exit(0);
    }

    /**
     * Asks the client to ask server for list of connected users.
     */
    private void list() {
        client.send(Protocol.LIST);
    }

    /**
     * Reads a String from the scanner and won't stop until the user input is not empty.
     * This is not true if client.pressEnter is true, refer to its documentation for more details.
     *
     * @return user's input
     */
    private String readNextLine() {
        while (true) {
            String text = scanner.nextLine();
            if (client.pressEnter) {
                return "";
            }
            if (!text.isEmpty()) {
                return text;
            }
        }
    }

    /**
     * Reads a number from the scanner and won't stop until the user input is a valid number.
     * This is not true if client.pressEnter is true, refer to its documentation for more details.
     *
     * @return user's input
     */
    private int readNextInt() {
        while (true) {
            try {
                String text = scanner.nextLine();
                if (client.pressEnter) {
                    return -1;
                }
                if (text.isEmpty()) {
                    continue;
                }
                return Integer.parseInt(text);
            } catch (NumberFormatException ignored) {
                print("Enter a valid number");
            }
        }
    }

    /**
     * Handles user inputs for the main menu and if appropriate switches to the queue menu.
     */
    private void runMainMenu() {
        print(MAIN_MENU);
        while (true) {
            int choice = readNextInt();
            switch (choice) {
                case 1 -> {
                    runQueueMenu();
                    return;
                }
                case 2 -> list();
                case 3 -> quit();
            }
        }
    }

    /**
     * Handles user inputs for the queue menu if appropriate starts the game and runs the game menu based on player.
     * If user cancels queue the main menu will be called again.
     */
    private void runQueueMenu() {
        queue();
        client.send(Protocol.QUEUE);
        print(IN_QUEUE);
        while (true) {
            int choice = readNextInt();
            switch (choice) {
                case 1 -> {
                    client.send(Protocol.QUEUE);
                    runMainMenu();
                    return;
                }
                case 2 -> list();
                case 3 -> quit();
                case -1 -> {
                    client.pressEnter = false;
                    if (client.getGame() == null) {
                        return;
                    }
                    if (client.getPlayer() instanceof HumanPlayer) {
                        runGameMenu();
                    } else {
                        runAIGameMenu();
                    }
                    return;
                }
            }
        }
    }

    /**
     * Handles user input and interactions with client for game menu if the player is a HumanPlayer.
     */
    private void runGameMenu() {
        print(client.getGame().toString());
        print(IN_GAME);
        if (client.getGame().getTurn() != client.getPlayer()) {
            print("Opponents turn");
        } else {
            client.printMoves();
        }
        while (true) {
            String choice = readNextLine();
            switch (choice) {
                case "a" -> list();
                case "b" -> quit();
                case "c" -> {
                    Player bot = new ComputerPlayer("bot", new MonteCarloStrategy(Difficulty.MEDIUM));
                    try {
                        List<Move> hints = bot.determineMove(client.getGame());
                        print("You could play: " + hints.get(0).getIndex());
                    } catch (NoValidMoves e) {
                        print("You have no valid moves.");
                    }
                }
                default -> {
                    try {
                        if (client.getGame() == null) {
                            client.pressEnter = false;
                            runMainMenu();
                            return;
                        }
                        if (client.getGame().getTurn() != client.getPlayer()) {
                            print("Wait for your turn");
                            continue;
                        }
                        List<Move> moves = client.getGame().combineMoves();
                        if (moves.isEmpty()) {
                            client.pressEnter = false;
                            client.sendMove(64);
                            continue;
                        }
                        int choiceIndex = Integer.parseInt(choice) - 1;
                        if (choiceIndex >= 0 && choiceIndex < moves.size()) {
                            client.sendMove(moves.get(choiceIndex).getIndex());
                        } else {
                            print("Enter a valid choice from the menu");
                        }
                    } catch (NumberFormatException ignored) {
                        print("Enter a valid choice from the menu");
                    }
                }
            }
        }
    }

    /**
     * Handles user input and interaction with client for game menu if player is a ComputerPlayer.
     */
    private void runAIGameMenu() {
        if (client.getPlayer().getMark() == Mark.BLACK) {
            print(client.getGame().toString());
            print(IN_GAME);
            client.printMoves();
            client.sendAIMove();
        } else {
            print("Waiting for the opponent");
        }
        while (true) {
            String choice = readNextLine();
            switch (choice) {
                case "a" -> list();
                case "b" -> quit();
                default -> {
                    if (client.getGame() == null) {
                        client.pressEnter = false;
                        runMainMenu();
                        return;
                    }
                }
            }
        }
    }

    /**
     * Handles user input for choosing difficulty menu and returns the chosen difficulty.
     *
     * @return chosen difficulty by user
     */
    private Difficulty runDifficultyMenu() {
        print(CHOOSE_DIFFICULTY);
        while (true) {
            int setting = readNextInt();
            switch (setting) {
                case 1:
                    return Difficulty.EASY;
                case 2:
                    return Difficulty.MEDIUM;
                case 3:
                    return Difficulty.HARD;
                default:
                    print("Select a valid difficulty.");
            }
        }
    }
}
