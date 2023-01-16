package tictactoe.ai;

import tictactoe.model.Game;
import tictactoe.model.Move;
import tictactoe.model.Player;

import java.util.List;

public class State {
    private Game game;
    private Player player;

    public Move moveToParent;

    private List<Move> unexploredMoves;

    /**
     * setting the player (or AI) as opponent should allow it to also
     * recommend moves to the player.
     *
     * @param game
     */
    public State(Game game, Move moveToParent) {
        this.moveToParent = moveToParent;
        this.game = game; //deepcopy?
        if (game != null) {
            this.unexploredMoves = game.getValidMoves();
            this.player = game.getTurn(); //change later
        }
    }

    public Game getGame() {
        return game;
    }

    public Player getPlayer() {
        return player;
    }

    public void randomMove() {
        NaiveStrategy strat = new NaiveStrategy();
        game.doMove(strat.determineMove(game));
    }

//    public Move getMoveToParent() {
//        return getMoveToParent();
//    }


    public List<Move> getUnexploredMoves() {
        return unexploredMoves;
    }


}
