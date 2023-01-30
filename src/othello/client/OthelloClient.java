package othello.client;

import othello.game.*;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.List;

public class OthelloClient implements Client, Runnable {

    private Socket socket;
    private final OthelloListener listener = new OthelloListener(this);
    private BufferedWriter bw;
    private String username;
    private Player player;
    private OthelloGame game;
    private boolean hasLoggedIn = false;

    public boolean pressEnter = false;

    public boolean connect(InetAddress address, int port) {
        try {
            socket = new Socket(address, port);
            bw = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            Thread thread = new Thread(this);
            thread.start();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

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
                                listener.printNewGameFound(protocolSplit[2]);
                            } else {
                                game = new OthelloGame(new HumanPlayer(protocolSplit[1]), player);
                                listener.printNewGameFound(protocolSplit[1]);
                            }
                        }
                        case Protocol.MOVE -> {
                            try {
                                int moveIndex = Integer.parseInt(protocolSplit[1]);
                                if (moveIndex == 64 && game.getTurn() != player) {
                                    listener.printOpponentSkipped();
                                } else {
                                    game.doMove(moveIndex);
                                }
                                game.nextTurn();
                                listener.printGame();
                                if (player instanceof ComputerPlayer) {
                                    sendAIMove();
                                }
                            } catch (NoValidMoves ignored) {
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

    public void close() {
        try {
            socket.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public boolean send(String msg) {
        try {
            bw.write(msg);
            bw.newLine();
            bw.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }
    }

    public void sendMove(int moveIndex) {
        if (game.isGameOver()) {
            return;
        }
        send(Protocol.sendMove(moveIndex));
    }

    public void sendAIMove() {
        try {
            if (game.isGameOver()) {
                return;
            }
            List<Move> moves = player.determineMove(game);
            int aiMoveIndex = moves.get(0).getIndex();
            sendMove(aiMoveIndex);
        } catch (NoValidMoves ignored) {
            sendMove(64);
        }

    }

    public List<Move> printMoves() {
        return listener.printMoves();
    }

    public boolean getLoggedIn() {
        return hasLoggedIn;
    }

    public Player getPlayer() {
        return player;
    }

    public void setPlayer(Player player) {
        this.player = player;
    }

    public String getUsername() {
        return username;
    }

    public void setUsername(String username) {
        this.username = username;
    }

    public OthelloGame getGame() {
        return game;
    }
}
