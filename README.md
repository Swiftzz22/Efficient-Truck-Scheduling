# Efficient Truck Scheduling (POSIX C)

A turn-based delivery scheduler written in C for my Operating Systems course at BITS Pilani, Goa.

## Problem
A fleet of trucks moves on a grid, picking up packages and delivering them before they expire. A central process publishes the world state each turn; trucks carrying cargo must present an authorization string, which is recovered by querying separate solver processes.

## Approach
- **IPC:** attaches to a shared-memory board (truck positions, package requests, commands) and communicates turn changes and solver queries over **System V message queues**.
- **Scheduling:** a greedy policy assigns each truck pick-up, drop-off and move commands per turn, scoring pick-ups by **urgency** (turns left before expiry) and drop-offs by **Manhattan distance**.
- **Auth strings:** when a truck moves with cargo, the program generates candidate strings and checks each guess with a solver process over a message queue.
- Tracks every package's lifecycle (waiting, picked up, delivered) and its assigned truck.

## Concepts
Shared memory, message queues, multi-process coordination, greedy scheduling under deadlines.

## Build & run
```bash
gcc -O2 -o scheduler solution.c
./scheduler
```
*(The central simulator and test inputs were provided by the course and are not included.)*
