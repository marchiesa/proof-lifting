function Sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

predicate ValidConfig(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] >= 0
}

predicate TakeStone(before: seq<int>, after: seq<int>)
{
  |before| == |after| &&
  exists i :: 0 <= i < |before| &&
    before[i] >= 1 &&
    after[i] == before[i] - 1 &&
    (forall j :: 0 <= j < |before| && j != i ==> after[j] == before[j])
}

predicate MoveStone(before: seq<int>, after: seq<int>)
{
  |before| == |after| &&
  exists i, j :: 0 <= i < |before| && 0 <= j < |before| && i != j &&
    before[i] >= 1 &&
    after[i] == before[i] - 1 &&
    after[j] == before[j] + 1 &&
    (forall k :: 0 <= k < |before| && k != i && k != j ==> after[k] == before[k])
}

predicate Step(before: seq<int>, after: seq<int>)
{
  TakeStone(before, after) || MoveStone(before, after)
}

ghost predicate Reachable(start: seq<int>, target: seq<int>)
{
  exists trace: seq<seq<int>> :: |trace| >= 1 && |trace| <= Sum(start) + 1 &&
    trace[0] == start &&
    trace[|trace| - 1] == target &&
    (forall i :: 0 <= i < |trace| ==> ValidConfig(trace[i])) &&
    (forall i :: 0 <= i < |trace| - 1 ==> Step(trace[i], trace[i + 1]))
}

method PilesWithStones(x: seq<int>, y: seq<int>) returns (result: bool)
  requires |x| == |y|
  requires ValidConfig(x)
  requires ValidConfig(y)
  ensures result == Reachable(x, y)
{
  var v_sum := 0;
  var i := 0;
  while i < |x| {
    v_sum := v_sum + x[i];
    i := i + 1;
  }

  var b_sum := 0;
  i := 0;
  while i < |y| {
    b_sum := b_sum + y[i];
    i := i + 1;
  }

  result := b_sum <= v_sum;
}

method Main() {
  // ========== SPEC POSITIVE TESTS ==========
  // (Reachable uses exists over seq<seq<int>> so it can't run at runtime;
  //  we test the building-block predicates with small inputs instead.)

  // ValidConfig
  expect ValidConfig([]), "spec positive 1: ValidConfig([])";
  expect ValidConfig([0]), "spec positive 2: ValidConfig([0])";
  expect ValidConfig([1, 2, 3]), "spec positive 3: ValidConfig([1,2,3])";
  expect ValidConfig([0, 0, 0]), "spec positive 4: ValidConfig([0,0,0])";
  expect ValidConfig([5, 3, 1]), "spec positive 5: ValidConfig([5,3,1])";

  // TakeStone: remove exactly one stone from one pile
  expect TakeStone([2, 1], [1, 1]), "spec positive 6: TakeStone take from pile 0";
  expect TakeStone([0, 3], [0, 2]), "spec positive 7: TakeStone take from pile 1";
  expect TakeStone([1], [0]), "spec positive 8: TakeStone single pile";
  expect TakeStone([3, 2, 1], [3, 1, 1]), "spec positive 9: TakeStone from middle pile";

  // MoveStone: move exactly one stone between two piles
  expect MoveStone([2, 1], [1, 2]), "spec positive 10: MoveStone 0->1";
  expect MoveStone([1, 0, 3], [0, 1, 3]), "spec positive 11: MoveStone 0->1 len3";
  expect MoveStone([1, 0, 3], [0, 0, 4]), "spec positive 12: MoveStone 0->2 len3";
  expect MoveStone([3, 1, 2], [3, 0, 3]), "spec positive 13: MoveStone 1->2";

  // Step: either take or move
  expect Step([2, 1], [1, 1]), "spec positive 14: Step via take";
  expect Step([2, 1], [1, 2]), "spec positive 15: Step via move";
  expect Step([5], [4]), "spec positive 16: Step take single pile";

  // ========== SPEC NEGATIVE TESTS ==========
  // ValidConfig: reject configs with negative values
  expect !ValidConfig([-1]), "spec negative 1: ValidConfig([-1])";
  expect !ValidConfig([1, -2, 3]), "spec negative 2: ValidConfig([1,-2,3])";
  expect !ValidConfig([0, -1]), "spec negative 3: ValidConfig([0,-1])";

  // TakeStone: reject invalid takes
  expect !TakeStone([2, 1], [2, 1]), "spec negative 4: TakeStone no change";
  expect !TakeStone([2, 1], [1, 0]), "spec negative 5: TakeStone both decreased";
  expect !TakeStone([2, 1], [3, 1]), "spec negative 6: TakeStone increased";
  expect !TakeStone([0], [0]), "spec negative 7: TakeStone can't take from 0";
  expect !TakeStone([2, 1], [0, 1]), "spec negative 8: TakeStone took 2 not 1";

  // MoveStone: reject invalid moves
  expect !MoveStone([2, 1], [2, 1]), "spec negative 9: MoveStone no change";
  expect !MoveStone([2, 1], [0, 3]), "spec negative 10: MoveStone moved 2 not 1";
  expect !MoveStone([1, 1], [0, 0]), "spec negative 11: MoveStone both decreased";
  expect !MoveStone([2, 1, 0], [1, 0, 0]), "spec negative 12: MoveStone two piles decreased";

  // Step: reject invalid transitions
  expect !Step([1, 1], [2, 2]), "spec negative 13: Step both increased";
  expect !Step([1, 2], [1, 2]), "spec negative 14: Step no change";
  expect !Step([1, 2], [1]), "spec negative 15: Step different lengths";
  expect !Step([1, 1], [3, 0]), "spec negative 16: Step moved 2 stones";

  // ========== IMPLEMENTATION TESTS ==========
  // Test 1: Yes
  var r1 := PilesWithStones([1, 2, 3, 4, 5], [2, 1, 4, 3, 5]);
  expect r1 == true, "impl test 1 failed";

  // Test 2: Yes
  var r2 := PilesWithStones([1, 1, 1, 1, 1], [1, 0, 1, 0, 1]);
  expect r2 == true, "impl test 2 failed";

  // Test 3: No
  var r3 := PilesWithStones([2, 3, 9], [1, 7, 9]);
  expect r3 == false, "impl test 3 failed";

  // Test 4: n=40, Yes
  var r4 := PilesWithStones(
    [361, 372, 139, 808, 561, 460, 421, 961, 727, 719, 130, 235, 320, 470, 432, 759, 317, 886, 624, 666, 917, 133, 736, 710, 462, 424, 541, 118, 228, 216, 612, 339, 800, 557, 291, 128, 801, 9, 0, 318],
    [364, 689, 60, 773, 340, 571, 627, 932, 581, 856, 131, 153, 406, 475, 217, 716, 433, 519, 417, 552, 919, 53, 923, 605, 319, 359, 516, 121, 207, 180, 373, 343, 905, 641, 477, 416, 927, 207, 160, 245]
  );
  expect r4 == true, "impl test 4 failed";

  // Test 5: n=45, Yes
  var r5 := PilesWithStones(
    [246, 523, 714, 431, 266, 139, 591, 246, 845, 818, 805, 198, 70, 620, 166, 478, 87, 849, 415, 228, 957, 59, 190, 332, 632, 14, 451, 857, 221, 638, 837, 222, 970, 643, 19, 172, 39, 185, 903, 342, 750, 265, 241, 968, 876],
    [460, 389, 541, 164, 324, 52, 246, 107, 826, 864, 693, 132, 10, 697, 429, 434, 99, 950, 164, 85, 972, 157, 327, 337, 592, 241, 350, 962, 130, 673, 967, 373, 657, 923, 456, 347, 394, 76, 743, 407, 724, 117, 268, 741, 918]
  );
  expect r5 == true, "impl test 5 failed";

  // Test 6: n=50, Yes
  var r6 := PilesWithStones(
    [620, 222, 703, 953, 303, 333, 371, 125, 554, 88, 60, 189, 873, 644, 817, 100, 760, 64, 887, 605, 611, 845, 762, 916, 21, 26, 254, 553, 602, 66, 796, 531, 329, 888, 274, 584, 215, 135, 69, 403, 680, 734, 440, 406, 53, 958, 135, 230, 918, 206],
    [464, 128, 878, 999, 197, 358, 447, 191, 530, 218, 63, 443, 630, 587, 836, 232, 659, 117, 787, 254, 667, 646, 498, 845, 252, 179, 452, 390, 455, 16, 686, 522, 236, 945, 498, 635, 445, 225, 7, 38, 553, 946, 563, 457, 102, 942, 130, 310, 941, 312]
  );
  expect r6 == true, "impl test 6 failed";

  // Test 7: n=40, No
  var r7 := PilesWithStones(
    [361, 372, 139, 808, 561, 460, 421, 961, 727, 719, 130, 235, 320, 470, 432, 759, 317, 886, 624, 666, 917, 133, 736, 710, 462, 424, 541, 118, 228, 216, 612, 339, 800, 557, 291, 128, 801, 9, 0, 318],
    [29, 469, 909, 315, 333, 412, 777, 490, 492, 431, 908, 412, 187, 829, 453, 595, 896, 817, 755, 914, 34, 890, 583, 691, 544, 969, 733, 132, 802, 170, 67, 68, 370, 146, 856, 184, 275, 785, 928, 798]
  );
  expect r7 == false, "impl test 7 failed";

  // Test 8: n=45, No
  var r8 := PilesWithStones(
    [246, 523, 714, 431, 266, 139, 591, 246, 845, 818, 805, 198, 70, 620, 166, 478, 87, 849, 415, 228, 957, 59, 190, 332, 632, 14, 451, 857, 221, 638, 837, 222, 970, 643, 19, 172, 39, 185, 903, 342, 750, 265, 241, 968, 876],
    [918, 332, 978, 856, 517, 621, 81, 62, 150, 482, 834, 649, 860, 259, 394, 937, 647, 0, 400, 783, 574, 713, 355, 221, 543, 389, 937, 824, 53, 361, 824, 454, 217, 180, 840, 407, 160, 417, 373, 737, 49, 476, 320, 59, 886]
  );
  expect r8 == false, "impl test 8 failed";

  // Test 9: n=50, No
  var r9 := PilesWithStones(
    [620, 222, 703, 953, 303, 333, 371, 125, 554, 88, 60, 189, 873, 644, 817, 100, 760, 64, 887, 605, 611, 845, 762, 916, 21, 26, 254, 553, 602, 66, 796, 531, 329, 888, 274, 584, 215, 135, 69, 403, 680, 734, 440, 406, 53, 958, 135, 230, 918, 206],
    [494, 447, 642, 337, 839, 128, 971, 105, 915, 739, 803, 8, 848, 253, 554, 186, 338, 656, 238, 106, 89, 13, 622, 777, 663, 669, 360, 451, 461, 639, 403, 255, 570, 648, 996, 618, 55, 409, 733, 230, 533, 226, 774, 559, 161, 184, 933, 308, 554, 161]
  );
  expect r9 == false, "impl test 9 failed";

  // Test 10: n=50, all 1000s -> all 1000s, Yes
  var r10 := PilesWithStones(
    [1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000],
    [1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000]
  );
  expect r10 == true, "impl test 10 failed";

  // Test 11: n=1, Yes
  var r11 := PilesWithStones([633], [609]);
  expect r11 == true, "impl test 11 failed";

  // Test 12: n=2, No
  var r12 := PilesWithStones([353, 313], [327, 470]);
  expect r12 == false, "impl test 12 failed";

  // Test 13: n=3, Yes
  var r13 := PilesWithStones([835, 638, 673], [624, 232, 266]);
  expect r13 == true, "impl test 13 failed";

  // Test 14: n=4, No
  var r14 := PilesWithStones([936, 342, 19, 398], [247, 874, 451, 768]);
  expect r14 == false, "impl test 14 failed";

  // Test 15: n=5, No
  var r15 := PilesWithStones([417, 666, 978, 553, 271], [488, 431, 625, 503, 978]);
  expect r15 == false, "impl test 15 failed";

  // Test 16: n=10, Yes
  var r16 := PilesWithStones(
    [436, 442, 197, 740, 550, 361, 317, 473, 843, 982],
    [356, 826, 789, 479, 641, 974, 106, 221, 57, 858]
  );
  expect r16 == true, "impl test 16 failed";

  // Test 17: n=15, Yes
  var r17 := PilesWithStones(
    [702, 593, 763, 982, 263, 48, 487, 759, 961, 80, 642, 169, 778, 621, 764],
    [932, 885, 184, 230, 411, 644, 296, 351, 112, 940, 73, 707, 296, 472, 86]
  );
  expect r17 == true, "impl test 17 failed";

  // Test 18: n=20, Yes
  var r18 := PilesWithStones(
    [82, 292, 379, 893, 300, 854, 895, 638, 58, 971, 278, 168, 580, 272, 653, 315, 176, 773, 709, 789],
    [298, 710, 311, 695, 328, 459, 510, 994, 472, 515, 634, 568, 368, 913, 182, 223, 361, 132, 92, 620]
  );
  expect r18 == true, "impl test 18 failed";

  // Test 19: n=25, No
  var r19 := PilesWithStones(
    [349, 443, 953, 126, 394, 160, 63, 924, 795, 450, 572, 513, 338, 33, 768, 34, 955, 737, 874, 731, 329, 16, 377, 318, 125],
    [56, 39, 740, 846, 938, 851, 459, 538, 617, 664, 268, 981, 315, 2, 23, 76, 974, 417, 786, 816, 207, 227, 870, 385, 958]
  );
  expect r19 == false, "impl test 19 failed";

  // Test 20: n=30, No
  var r20 := PilesWithStones(
    [722, 523, 950, 656, 431, 347, 463, 795, 893, 348, 208, 893, 140, 65, 419, 36, 627, 333, 972, 346, 230, 422, 337, 893, 896, 442, 835, 56, 846, 986],
    [429, 148, 890, 854, 546, 680, 776, 265, 551, 465, 387, 823, 996, 845, 374, 867, 411, 742, 447, 267, 711, 989, 501, 694, 456, 451, 192, 529, 215, 709]
  );
  expect r20 == false, "impl test 20 failed";

  print "All tests passed\n";
}
