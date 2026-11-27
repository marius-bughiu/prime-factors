import PrimeFactors.PartialOrder
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-! Two 1024-bit primes immediately below the public endpoint 2^1024.
The candidates and modular-order witnesses below were generated in this project.
For the 55-bit offset use 2^4 * 6355^4 - 1. The predecessor factors as
2^4 * (2^255 - 6355) * (2^255 + 6355) * (2^510 + 6355^2).
For the 60-bit offset let v = 2^4 * 3451^2 - 1. The offset is 2^4 * v^2 - 1.
Its prime has a predecessor divisible by 2^4 * (2^510 - v), and the latter
prime has predecessor 2^4 * (2^253 - 3451) * (2^253 + 3451).
Trial division and GNU Coreutils factor supplied divisors of these algebraic
pieces and smaller predecessors. GMP screened candidates. Lean certifies every
primality claim through the repository's partial-order criterion. -/
namespace PrimeFactors.NearEndpointPrimes

set_option exponentiation.threshold 2048
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

abbrev smallerOffset : ℕ := 26096496244809999
abbrev largerOffset : ℕ := 580951370506755599

private theorem quotient_unit {n e v : ℕ} {z : ZMod n}
    (value : z^e=(v : ZMod n)) (coprime : Nat.Coprime ((v : ZMod n)-1).val n) :
    Nat.Coprime (z^e-1).val n := by rwa [value]

private theorem certify {n F : ℕ} (z : ZMod n) {ps : List ℕ}
    (size : 1<n ∧ 0<F ∧ n≤F^2) (cover : Covers F ps) (full : z^F=1)
    (proper : ∀ q∈ps, Nat.Coprime (z^(F/q)-1).val n) : n.Prime :=
  prime_of_partial_order_cover z size.1 size.2.1 size.2.2 cover full proper

private theorem order0 : Nat.Prime 16981 := by
  apply certify (12470 : ZMod _) (F:=283) (ps:=[283]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 283) covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=12470) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order1 : Nat.Prime 18959 := by
  apply certify (169 : ZMod _) (F:=9479) (ps:=[9479]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 9479) covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=169) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order2 : Nat.Prime 38393 := by
  apply certify (6561 : ZMod _) (F:=4799) (ps:=[4799]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 4799) covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=6561) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order3 : Nat.Prime 81457 := by
  apply certify (75528 : ZMod _) (F:=1697) (ps:=[1697]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 1697) covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=75528) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order4 : Nat.Prime 153841 := by
  apply certify (98945 : ZMod _) (F:=641) (ps:=[641]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 641) covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=98945) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order5 : Nat.Prime 189529 := by
  apply certify (49200 : ZMod _) (F:=1272) (ps:=[53, 2, 3]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 53) (Covers.cons 3 (by norm_num : Nat.Prime 2) (Covers.cons 1 (by norm_num : Nat.Prime 3) covers_one))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact quotient_unit (v:=9674) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=189528) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=161392) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order6 : Nat.Prime 244091 := by
  apply certify (174844 : ZMod _) (F:=770) (ps:=[11, 7, 5, 2]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 11) (Covers.cons 1 (by norm_num : Nat.Prime 7) (Covers.cons 1 (by norm_num : Nat.Prime 5) (Covers.cons 1 (by norm_num : Nat.Prime 2) covers_one)))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact quotient_unit (v:=145534) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=25742) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=80902) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=244090) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order7 : Nat.Prime 332183 := by
  apply certify (134746 : ZMod _) (F:=4051) (ps:=[4051]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 4051) covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=134746) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order8 : Nat.Prime 436181 := by
  apply certify (61849 : ZMod _) (F:=1130) (ps:=[113, 5, 2]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 113) (Covers.cons 1 (by norm_num : Nat.Prime 5) (Covers.cons 1 (by norm_num : Nat.Prime 2) covers_one))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact quotient_unit (v:=224217) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=431704) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=436180) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order9 : Nat.Prime 838913 := by
  apply certify (635750 : ZMod _) (F:=7424) (ps:=[2, 29]) (by decide +kernel)
    (Covers.cons 8 (by norm_num : Nat.Prime 2) (Covers.cons 1 (by norm_num : Nat.Prime 29) covers_one)) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · exact quotient_unit (v:=838912) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=314926) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order10 : Nat.Prime 1952729 := by
  apply certify (6561 : ZMod _) (F:=244091) (ps:=[244091]) (by decide +kernel)
    (Covers.cons 1 order6 covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=6561) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order11 : Nat.Prime 2461457 := by
  apply certify (1201952 : ZMod _) (F:=153841) (ps:=[153841]) (by decide +kernel)
    (Covers.cons 1 order4 covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=1201952) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order12 : Nat.Prime 85920077 := by
  apply certify (50278666 : ZMod _) (F:=1952729) (ps:=[1952729]) (by decide +kernel)
    (Covers.cons 1 order10 covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=50278666) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order13 : Nat.Prime 344041519 := by
  apply certify (74965910 : ZMod _) (F:=19743) (ps:=[6581, 3]) (by decide +kernel)
    (Covers.cons 1 (by norm_num : Nat.Prime 6581) (Covers.cons 1 (by norm_num : Nat.Prime 3) covers_one)) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · exact quotient_unit (v:=306053913) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=308842490) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order14 : Nat.Prime 47541984277 := by
  apply certify (13150425650 : ZMod _) (F:=436181) (ps:=[436181]) (by decide +kernel)
    (Covers.cons 1 order8 covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=13150425650) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order15 : Nat.Prime 597085786153 := by
  apply certify (174202145092 : ZMod _) (F:=916974) (ps:=[16981, 3, 2]) (by decide +kernel)
    (Covers.cons 1 order0 (Covers.cons 3 (by norm_num : Nat.Prime 3) (Covers.cons 1 (by norm_num : Nat.Prime 2) covers_one))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact quotient_unit (v:=168324827464) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=29176852761) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=597085786152) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order16 : Nat.Prime 13320820223832554549 := by
  apply certify (1782501948796141309 : ZMod _) (F:=6927743554) (ps:=[838913, 4129, 2]) (by decide +kernel)
    (Covers.cons 1 order9 (Covers.cons 1 (by norm_num : Nat.Prime 4129) (Covers.cons 1 (by norm_num : Nat.Prime 2) covers_one))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact quotient_unit (v:=7455938504260928089) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=12123620599864868433) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=13320820223832554548) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order17 : Nat.Prime 863792213210964389766694846988843401 := by
  apply certify (285133049363545583274540253808892424 : ZMod _) (F:=13320820223832554549) (ps:=[13320820223832554549]) (by decide +kernel)
    (Covers.cons 1 order16 covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=285133049363545583274540253808892424) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order18 : Nat.Prime 2316888112114183783777432697885988189081714148650593 := by
  apply certify (700811109157266776204033310759602288051604535439242 : ZMod _) (F:=863792213210964389766694846988843401) (ps:=[863792213210964389766694846988843401]) (by decide +kernel)
    (Covers.cons 1 order17 covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=700811109157266776204033310759602288051604535439242) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order19 : Nat.Prime 5850814682770338369777306100312930410383703743436759563 := by
  apply certify (1998082595647441801758455105054703041663074541016820110 : ZMod _) (F:=13948794945296103744433903889) (ps:=[344041519, 85920077, 332183, 38393, 37]) (by decide +kernel)
    (Covers.cons 1 order13 (Covers.cons 1 order12 (Covers.cons 1 order7 (Covers.cons 1 order2 (Covers.cons 1 (by norm_num : Nat.Prime 37) covers_one))))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact quotient_unit (v:=3358928077003258277798486484973179196010336518387021456) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=726924080593776851869962817581650763547060103035167217) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=2163570145077525921752573220483740413024738219466234781) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=5822008775189712961381888424064152791595515615955901604) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=3659265631201224429898021577296808743926039269431467846) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order20 : Nat.Prime 2554215759374945731592121732658686308186657275979015449294326407 := by
  apply certify (649115755379526257567475709974483101796543307727562586713976656 : ZMod _) (F:=158276928666408346821170125857031) (ps:=[597085786153, 47541984277, 189529, 73, 31, 13]) (by decide +kernel)
    (Covers.cons 1 order15 (Covers.cons 1 order14 (Covers.cons 1 order5 (Covers.cons 1 (by norm_num : Nat.Prime 73) (Covers.cons 1 (by norm_num : Nat.Prime 31) (Covers.cons 1 (by norm_num : Nat.Prime 13) covers_one)))))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact quotient_unit (v:=1710825538439285474221921525739457895857267475464724476320369448) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=866354926544790939383904382272812214618694831891742204659158167) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=829743969803154640833070471359227565876404431530218819303551323) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=460138784759305916057949820895281667826903710951765747507205508) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=2335671544581841370235881688510503162074803825657201895937339033) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=2414369415849150499662974352193348999440026696061023294701860881) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order21 : Nat.Prime 17339336513524437769327790507440537264640608665115388445561183589085524057 := by
  apply certify (2502135782271585670368682625765556262979182080627857250320914157201193439 : ZMod _) (F:=5850814682770338369777306100312930410383703743436759563) (ps:=[5850814682770338369777306100312930410383703743436759563]) (by decide +kernel)
    (Covers.cons 1 order19 covers_one) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact quotient_unit (v:=2502135782271585670368682625765556262979182080627857250320914157201193439) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

private theorem order22 : Nat.Prime 3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412060970609 := by
  apply certify (2425617937193679854225110121742135369990252255922504307509422494860811377584974201576877293624638982369683614021756017924724104038522720559806408383619238 : ZMod _) (F:=231584178474632390847141970017375815706539969331281128078915168015826259224656) (ps:=[2316888112114183783777432697885988189081714148650593, 2461457, 81457, 18959, 479, 191, 71, 23, 2, 11]) (by decide +kernel)
    (Covers.cons 1 order18 (Covers.cons 1 order11 (Covers.cons 1 order3 (Covers.cons 1 order1 (Covers.cons 1 (by norm_num : Nat.Prime 479) (Covers.cons 1 (by norm_num : Nat.Prime 191) (Covers.cons 1 (by norm_num : Nat.Prime 71) (Covers.cons 1 (by norm_num : Nat.Prime 23) (Covers.cons 4 (by norm_num : Nat.Prime 2) (Covers.cons 1 (by norm_num : Nat.Prime 11) covers_one)))))))))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact quotient_unit (v:=2299205851428210945331129615316110862696213553111561027747987049893354409629916147201617753338157421959282399368160308724927944401348369622114774119149550) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=2571566531243378920051844389366547812704909513576889242627295228595447633851833717606209832253473955004701010703424706517551377639538207504290532760745790) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=2505954057277927045632187182567232648338608448766247219359716243871011574807330005823921466133831092020218967499181766837013262121730502207358901543594616) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=177770270679106170321641700770380152598646106956162715085083956015903720477180081012029588718356955633175553255345430493593967805842747623635400661501126) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=2067117159591418703977585828016648918891708961592811151539136831625995596419418741973780040323883479337795868828559591144962827058743117878418546857271449) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=705155758301554550965073103217518028174667939807297600209590114683338692674031889751243121370002738760789737222916037064032463007808041459162954383312893) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=733213231131633956032987196439416179500781239853672172623168933293000554613512220161208504410247153529798167491635985807942238544802992467584505641531812) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=320592918237091947171688005908351633503156983311757898230457529243859818231461070272742304886219576950340041876939374132932859258606179416763010336794004) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412060970608) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=3093146702196365810289295330103607565970067028960142665437362819946284885070981637724693002917306814375540273549374080323850304093867065486694842305174533) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

theorem largerOffset_prime : Nat.Prime (2^1024-largerOffset) := by
  change Nat.Prime 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304834775378253717381617
  apply certify (28593086874994872422520191787828538045057092581958998059300075543425013171409892225103010046095592743618238009196619809437754093705872059256348192441938800468394472604218037478661017481890214695943472215311349293703616109109701971437202803243278909382053156119666031369956907542973353978309815773261747773585 : ZMod _) (F:=26815615859885194199148049996411692254958731641184786755447122887443528060147093953603748596333806855380063716372972101707507765623893139892867296487764872) (ps:=[3351951982485649274893506249551461531869841455148098344430890360930441007518386744200468574541725856922507964546621512713438470702986642486608412060970609, 2]) (by decide +kernel)
    (Covers.cons 1 order22 (Covers.cons 3 (by norm_num : Nat.Prime 2) covers_one)) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · exact quotient_unit (v:=165062674563022427332024335524167459617522690680660179480749987715121305923008534478418845520649742785815985992108758328782349404465480751599789787031161954775247028892258310253322653751964582390344937768705119544027436237463779806727266812985416653032266088094666987310625160039839168696955665321222440095781) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304834775378253717381616) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

theorem smallerOffset_prime : Nat.Prime (2^1024-smallerOffset) := by
  change Nat.Prime 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835330233127979327217
  apply certify (120129055058139380752166173105363093710418634538631553769110016650403243997011726860887221690985504395783501594646552729819485415126924841018779265949488035196890574457782695196042583163573514628880285352486940475738650149365595218274942420727578250737432081542867127381829247089189239403840895682932802368025 : ZMod _) (F:=183618504092383235466156434441212422082294348822906115627885512137593900642162504041618300838829749854399224105198560727434057273978012515897891006027700369) (ps:=[17339336513524437769327790507440537264640608665115388445561183589085524057, 2554215759374945731592121732658686308186657275979015449294326407, 4349, 1019, 577, 439, 317, 191, 61]) (by decide +kernel)
    (Covers.cons 1 order21 (Covers.cons 1 order20 (Covers.cons 1 (by norm_num : Nat.Prime 4349) (Covers.cons 1 (by norm_num : Nat.Prime 1019) (Covers.cons 1 (by norm_num : Nat.Prime 577) (Covers.cons 1 (by norm_num : Nat.Prime 439) (Covers.cons 1 (by norm_num : Nat.Prime 317) (Covers.cons 1 (by norm_num : Nat.Prime 191) (Covers.cons 1 (by norm_num : Nat.Prime 61) covers_one))))))))) (by reduce_mod_char)
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact quotient_unit (v:=130097683713934028100370569763613828045681524827044264240985157760463650738917705174983616197615622091666355566270255632596897474188990906559684197627489945263081660318263185807064623903192392145394632789367353099180346556985350908700613141252600067332441250755879184065863452400555246084835318808095958875383) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=164673573747542480193286775674570883392350772248078293884275702901414996589453519723530716457451226655508678492339769876614856451274349733888060923494533338849152042093476108032730925853884181118765452946535019175527466824456767720515663404176104069639755803618342400090181459704538916681001735083734401171063) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=1623945274100752882782274347123086994328064888990970023329311128056077715458175364992535699235632637605789710350036216132610076967760157497752570725638356265801096055490620729930384528299346484450642534246422843044230967142204025599095386043079119789727630332915893601681929885190467743516062125520414912816) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=106750317135488795355057498972968102054474904369314632740109846403338363078817470879888244954437518899439487904748138984653694661139317913734357158729906183191287069697926927416621276200134416310072832721234218970910833006206266966926070352819086908239361772703657560506069967423378983409768572317978233258968) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=157779811296797159826226386374743493394736150930295764759471338336088484547010575262180658664400887340932223537031915956456578425961096251624294898560464032377487877996947950030286316861962465596400616261691905778216354897634932263837879978192938614909566279876877975322064253425341388428020426426640522597631) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=6792817525561519789574906672802009825935915811712128641466219127000687870736903966628462337144416968695373365320145443221729998763370950868236455413778257210758307531316743510331324036457767264026936290929898773688763625713579281785428819410390191145562438752254143795047903550882785391934860468559835376391) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=93754906593824316806947024155616722160262897676666666873130655178291307020375876577264804919594925798058401540855641800404794289487189980121210623476923313096725811319129399242945484954107319162526071837909386151184489377459340422971914792579265792598394983977479906431062125350905990114130853249412210835741) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=179459086197351592025113148980124020142012240013364495273635392276581442444762771839249185666088071493992250049036543315826330535006903432777155575561810365697481622409730256766546097380349500927405296567053627938092352935292220483883944064974917183940768111515209756827063637384079699257810990480640584427650) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)
  · exact quotient_unit (v:=124338241413674716862147660314072495179345175525942321765816272168152531014433356060943998117828428741669953125520202400254160540406715167813450794792690675619117543481446212938318020330186471123996517884714952298435065671765359138405129468954671403953604368719301786266077755456526123575781008811323100901381) (by simp only [Nat.reduceDiv]; reduce_mod_char) (by decide +kernel)

end PrimeFactors.NearEndpointPrimes
