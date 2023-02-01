package othello.server;

import java.util.InputMismatchException;
import java.util.Scanner;

/**
 * Class for running the TUI and managing OthelloServer
 */
public class OthelloServerApp {
    private OthelloServer server;

    /**
     * Create the server and run tui
     *
     * @param args system arguments
     */
    public static void main(String[] args) {
        OthelloServerApp app = new OthelloServerApp();
        app.createServer();
        app.runTui();
    }

    /**
     * Takes the port from user and if valid creates a server
     */
    private void createServer() {
        Scanner scan = new Scanner(System.in);
        while (true) {
            try {
                System.out.println("Please enter a valid port number 0-65536");
                int port = Integer.parseInt(scan.nextLine());
                if (port < 0 || port > 65536) {
                    throw new InvalidPortException();
                }
                server = new OthelloServer(port);
                server.start();
                System.out.printf("Created a server at: %s%n", port);
                break;
            } catch (InvalidPortException | InputMismatchException | NumberFormatException e) {
                System.out.println(e.getMessage());
            }
        }
    }

    /**
     * Manage TUI by taking user input and doing port, address, queue and quit commands
     */
    private void runTui() {
        Scanner scan = new Scanner(System.in);
        System.out.println("Type help to see the menu");
        while (true) {
            String arg = scan.nextLine();
            switch (arg) {
                case "quit" -> {
                    server.stop();
                    System.exit(0);
                }
                case "port" -> System.out.println(server.getPort());
                case "address" -> System.out.println(server.getAddress());
                case "queue" -> System.out.println(server.getQueueSize());
                case "help" ->
                        System.out.println("List of commands:\nport: print server's port\naddress: print server's address\nqueue: print the Othello queue");
                default -> System.out.println("invalid command");
            }
        }
    }
}
