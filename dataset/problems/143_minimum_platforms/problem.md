# Minimum Platforms

## Description

Given arrival and departure times of trains, find the minimum number of
platforms needed so no train waits (maximum simultaneous trains).

## Input

- `arrivals`, `departures`: sequences of times with `arrivals[i] <= departures[i]`

## Output

Maximum number of trains present at any point in time.

## Examples

- `MinPlatforms([100, 300, 350], [200, 400, 500])` returns `2`
