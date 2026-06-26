# 🌌 StarBlazer

[![Play on GitHub Pages](https://img.shields.io/badge/Play%20Now-GitHub%20Pages-success?style=for-the-badge&logo=github)](https://Slangnes.github.io/Star-blazer/)

A premium, two-player hexagonal strategy game of spatial placement, movement, and encirclement. Play against a friend locally, test your strategies against individual AI players, or sit back and watch two AIs play in attract mode.

## 🎮 How to Play

### The Objective
Your goal is to completely **surround the opponent's Royal (Queen) chip** so that it cannot slide or move to any adjacent empty space. 
* **Note:** A space is considered blocked if it is physically occupied by a chip, or if a physical slide path to that space is blocked by mutual neighbors ("freedom to slide" rule).

### Game Rules
1. **Initial Placement**: The first chip must be placed at the center of the board.
2. **Subsequent Placements**: When placing a new chip from your reserve, it must be placed adjacent to at least one of your own chips, and must not touch any of the opponent's chips.
3. **Movement**: Once a piece is on the board, it can move to other positions as long as the entire group of chips remains connected (the **One-Hive rule**). Unlike placements, movement can place your chip adjacent to opponent pieces.
4. **Royal Placement**: You must place your Royal chip within your first 4 turns.

---

## 🛡️ The Pieces

| Piece | Icon | Reserve | Movement Description |
| :--- | :---: | :---: | :--- |
| **Royal** | ♛ | 1 | Moves exactly **1 space** per turn. Must be protected at all costs. |
| **Soldier** | 🛡 | 3 | Slides any distance around the **perimeter** of the hive. |
| **Corvette** | ⎈ | 2 | Moves **1 space** per turn, but can **climb on top** of adjacent pieces and walk across the stack. Exempt from sliding restrictions. |
| **Hopper** | ⬦ | 3 | **Jumps in a straight line** over one or more chips to the first empty space. Exempt from sliding restrictions. |
| **General** | ★ | 2 | Slides a **maximum of 3 spaces** along the perimeter. |

---

## 🤖 Features & Settings

* **Individual AI Controllers**: Select `👤 Human` or `🤖 AI Player` on either player's card to set up local PvP, PvE, or spectator EvE games.
* **Smart Board Indicators**: Highlighting cells show valid placement options and possible movement targets automatically.
* **Responsive Design**: Visual indicators for active turns, hover states, and smooth panning/zooming.
* **Undo & New Game**: Easily revert misplays or start a fresh match.
