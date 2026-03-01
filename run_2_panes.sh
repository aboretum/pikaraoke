#!/bin/bash
SESSION_NAME="myproject"
APP1_CMD="./start_pi.sh"
APP2_CMD="./.venv/bin/python3 run_qr_code.py"

# Start a new detached tmux session named "myproject"
tmux new-session -d -s $SESSION_NAME

# Split the initial window horizontally (or use -v for vertical)
# The -t flag targets the specific session/window (0) and pane (0)
tmux split-window -h -t ${SESSION_NAME}:0.0 -l 15

# Send the command to the first pane (pane 0) and press Enter
tmux send-keys -t ${SESSION_NAME}:0.0 "$APP1_CMD" ENTER

# Send the command to the second pane (pane 1) and press Enter
tmux send-keys -t ${SESSION_NAME}:0.1 "$APP2_CMD" ENTER

# Attach to the created session to view the running applications
tmux attach-session -t $SESSION_NAME:0.0
