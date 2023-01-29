package othello.client;

import othello.ai.Difficulty;
import othello.ai.MonteCarloStrategy;
import othello.ai.NaiveStrategy;
import othello.game.*;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Scanner;

public class OthelloApp {
    private final OthelloClient client;
    private final Scanner scanner;

    private static final String MAIN_MENU = "quit"; // QUEUE LIST QUIT
    private static final String IN_QUEUE = ""; // CANCEL-QUEUE LIST QUIT
    private static final String IN_GAME = "queue"; // CHOOSE-MOVES LIST QUIT
    private static final String CHOOSE_PLAYER = "list"; // HUMAN,RANDOM-AI,SMART-AI
    private static final String CHOOSE_DIFFICULY = ""; //

    public OthelloApp(OthelloClient client) {
        this.client = client;
        scanner = new Scanner(System.in);
    }

    public static void main(String[] args) {
        OthelloApp tui = new OthelloApp(new OthelloClient());
        tui.run();
    }

    private void run() {
        String username = connectClient();
        login(username);


        print(client.getGame().toString());
        List<Move> moves = printMoves();
        print(IN_GAME);
        boolean inGameMenu = true;
        while (inGameMenu) {
            String choice = readNextLine();
            switch (choice) {
                case "a" -> list();
                case "b" -> quit();
                default -> {
                    try {
                        int moveIndex = Integer.parseInt(choice) - 1;
                        if (moveIndex >= 0 && moveIndex < moves.size()) {
                            client.send(Protocol.sendMove(moveIndex));
                            inGameMenu = false;
                        }
                    } catch (NumberFormatException ignored) {
                        print("Enter a valid choice from the menu");
                    }
                }
            }
        }
    }

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
            } catch (UnknownHostException ignored) {
                print("Cannot connect to the server with specified port");
            }
        }
    }

    private void login(String username) {
        while (true) {
            client.send(Protocol.sendLogin(username));
            if (client.getLoggedIn()) {
                client.setUsername(username);
                break;
            }
            print("Choose a different username");
            username = readNextLine();
        }
    }

    private void print(String msg) {
        System.out.printf("%s%n", msg);
    }

    private List<Move> printMoves() {
        return null;
    }

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
                    client.setPlayer(new ComputerPlayer(new NaiveStrategy()));
                    return;
                }
                case 3 -> {
                    client.setPlayer(new ComputerPlayer(new MonteCarloStrategy(runDifficultyMenu())));
                    return;
                }
                case 4 -> list();
                case 5 -> quit();
            }
        }
    }

    private void quit() {
        print("Exiting the Othello client. thank you for playing :)");
        System.exit(0);
    }

    private void list() {

    }

    private String readNextLine() {
        while (true) {
            String text = scanner.nextLine();
            if (!text.isEmpty()) {
                return text;
            }
        }
    }

    private int readNextInt() {
        while (true) {
            try {
                String text = scanner.nextLine();
                if (text.isEmpty()) {
                    continue;
                }
                return Integer.parseInt(text);
            } catch (NumberFormatException ignored) {
                print("Enter a valid number");
            }
        }
    }

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

    private void runQueueMenu() {
        queue();
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
            }
        }
    }

    private void runGameMenu() {
        print(client.getGame().toString());
    }

    private Difficulty runDifficultyMenu() {
        print("Select a difficulty: easy, mid (medium), hard");
        String setting = readNextLine();
        while (true) {
            switch (setting) {
                case "easy":
                    return Difficulty.EASY;
                case "mid":
                    return Difficulty.MEDIUM;
                case "hard":
                    return Difficulty.HARD;
                default:
                    print("Select a valid difficulty.");
            }
        }
    }
}
