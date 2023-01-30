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

    private static final String MAIN_MENU = "1) Queue\n2) List\n3) Quit";
    private static final String IN_QUEUE = "1) Cancel Queue\n2) List\n3) Quit";
    public static final String IN_GAME = "a) List\nb) Quit";
    private static final String CHOOSE_PLAYER = "1) Human\n2) Random-AI\n3) Smart-AI";
    private static final String CHOOSE_DIFFICULTY = "1) Easy\n2) Medium\n3) Hard";

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

        runMainMenu();
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
            } catch (UnknownHostException | IllegalArgumentException ignored) {
                print("Cannot connect to the server with specified port");
            }
        }
    }

    private void login(String username) {
        while (true) {
            client.send(Protocol.sendLogin(username));
            try {
                Thread.sleep(3000);
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

    private void print(String msg) {
        System.out.printf("%s%n", msg);
    }

    private List<Move> printMoves() {
        List<Move> moves = client.getGame().combineMoves();
        for (int i = 0; i < moves.size(); i++) {
            print(String.format("%s) %s", i + 1, moves.get(i).getIndex()));
        }
        return moves;
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

    private void quit() {
        print("Exiting the Othello client. thank you for playing :)");
        System.exit(0);
    }

    private void list() {
        client.send(Protocol.LIST);
    }

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

    private void runAIGameMenu() {
        print(client.getGame().toString());
        print(IN_GAME);
        if (client.getGame().getTurn() != client.getPlayer()) {
            print("Opponents turn");
        } else {
            client.printMoves();
            client.sendAIMove();
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
