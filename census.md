# Bidirectionality census — first tranche

Date: 2026-11-19

Campaign evidence only. Nothing in this file is a theorem.

Method: a system yields a contract by analysis (capabilities from its record, designs from its steps); synthesis builds the canonical system from a contract (the record equal to the capabilities, one premise free step per design); the round trip checks that analysis after synthesis after analysis equals analysis. Measures: description size (the capabilities count plus the designs count), semantic mass (distinct names), and bounds over subject lists (fold minimum and fold maximum, attained by construction).

## The executed run

The run is the script beside this file, with its raw output saved beside this file as well. It ran with the standard library only and exited clean. Its subjects are the three sibling proof repos named in the table by their short names from their records: losses, persistence, profiling.

| subject | pin | caps count | designs count | desc | mass | round trip verdict | bound role |
|---|---|---|---|---|---|---|---|
| losses | 12ee66e9c9cdaeec4bea5eb8fb1fd61e6df780fb | 13 | 3 | 16 | 16 | pass | low bound for desc and for mass |
| persistence | eb01cf2e33a20bfbda5a03aba7a48c70fbd10741 | 26 | 5 | 31 | 31 | pass | high bound for desc and for mass |
| profiling | a53c4bf5aa83e8677ecb66571d61ed4c11e2d88d | 16 | 3 | 19 | 19 | pass | interior on both measures |

State space comparison, per subject: losses desc 16 against 65536, and 16 is below it; persistence desc 31 against 2147483648, and 31 is below it; profiling desc 19 against 524288, and 19 is below it. The second number in each pair is two raised to the desc power.

Bounds over the three subjects: for desc, low 16 attained by losses and high 31 attained by persistence; for mass, low 16 attained by losses and high 31 attained by persistence. Every subject lies within both bound pairs, as the raw output shows line by line.

What these numbers are, stated exactly: these are measured numbers about name lists. The inventories are the core theorem names and the control names taken verbatim from each subject record (losses: thirteen core and three controls, from its synthesis section; persistence: twenty six core and five controls, thirty one audited declarations in all; profiling: sixteen core and three controls). The claim they evidence is only that the round trip and the bound machinery execute and agree on real inventories. Contract fidelity for real qualifications is gap G4 of the program, not settled by this run.

## Family subjects

Every repo under the account whose name begins with the software prefix, read through the account repo list (limit 400 per the brief; the same set of nineteen was read again at limit 1000 over 569 repos in all). Head pins were read one repo at a time through the head commit read. Date on every row: 2026-11-19. Kind follows the repo own stated work: a synthesis repo is one whose stated work is composing or synthesizing other subjects; the rest are proof repos, carrying theorem inventories. For the three measured subjects the status carries the run numbers; for the rest the blocking step is named in the status.

| name | pin | date | kind | status |
|---|---|---|---|---|
| software-benchmarking-is-redundant-and-suboptimal | a85286acc1f62c12992aa3a0ac8dee529b62927d | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-compilers-lose-info | 69358971221d66e6304b64ff68a2e111d15231b3 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-doesnt-have-to-regress | 858a85e383fbecc9826186aee2cc0101aea5ea62 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-doesnt-need-review | 1d504014be0c727b3f12e4d8e17f47dfceb118b6 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-frontier-is-solvable | 22418d56604c96fdc1ba2875f3167e228b6ac6f3 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-fuzzing-is-suboptimal | 6ed7a59651ae9dab006b7903a98d3d598cca19ea | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-a-closed-loop | f2c3b6d643bba02e90fb16381d20c9b891210e65 | 2026-11-19 | synthesis repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-bidirectional | empty — no head commit; the head read returned the empty repository error | 2026-11-19 | synthesis repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-composable | 7b1746467a410e9e5ae309f2a86bc4cd37700989 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-incrementally-certifiable | 3690167318cf4d41b51d0945f4fccc7f043e8412 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-incrementally-safe | 97e55d28edc0d33f3466de3a3e4061e010c3b4d5 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-more-traceable-than-you-think | 8f6a128069d0e68e97c4a69d78689c84350b0d2f | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-quantifiable | d88acbdc3ba78fff994067d2c73bcc01622b3f61 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-is-solvable | 3053b78d24bd81299e998bc253c755ab4a5e9b43 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-losses-are-compositional | 12ee66e9c9cdaeec4bea5eb8fb1fd61e6df780fb | 2026-11-19 | proof repo | MEASURED — caps 13, designs 3, desc 16, mass 16, round trip pass |
| software-optimality | 95df5fb7e922e7316b0ebe90b7847fd45a208d88 | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |
| software-persistence-is-minimal | eb01cf2e33a20bfbda5a03aba7a48c70fbd10741 | 2026-11-19 | proof repo | MEASURED — caps 26, designs 5, desc 31, mass 31, round trip pass |
| software-profiling-is-synthesizable | a53c4bf5aa83e8677ecb66571d61ed4c11e2d88d | 2026-11-19 | proof repo | MEASURED — caps 16, designs 3, desc 19, mass 19, round trip pass |
| software-testing-is-redundant | 18feb7ab60d542007124405fd8e1dc209c68361a | 2026-11-19 | proof repo | UNMEASURED — round-trip extraction not yet run for this subject; its theorem inventory is the extraction source |

One finding in this table, stated plainly: the bidirectional repo itself is empty at the time of this census — it exists, and it has no head commit yet. Its row carries that fact instead of a pin.

## The library census

The library repo is the one named idol-lib under the same account, verified through the same route. Head pin: 69ee40eb000f557e07dae548efa9a503703ecb35. Date: 2026-11-19. Its full tree, read recursively, holds 1067 entries (976 files and 91 folders). Its top level holds 20 entries: 4 files and 16 folders. The folders are the library entries, one row each below (sixteen rows, within the row per entry limit). The first tranche plan for this repo, stated once and carried by every row: each folder entry is a subject in waiting; its row converts only when extraction from its sources is mechanized and a checker run over its corpus lands. Every row below is UNMEASURED, and every row carries the same blocking step, named exactly: contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too).

| entry | pin | date | status | blocking step |
|---|---|---|---|---|
| adler32 | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| base64 | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| cbor | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| crc32 | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| jq | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| json | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| lz4 | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| md5 | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| msgpack | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| port | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| qoi | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| sha1 | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| sha256 | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| snappy | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| tools | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |
| xxhash | 69ee40eb000f557e07dae548efa9a503703ecb35 | 2026-11-19 | UNMEASURED | contract extraction from Idol sources is not mechanized; the end-to-end checker run over corpora is the open run (it is the persistence program's standing remainder too) |

Growth rule: the list only grows; each row carries pin and date; a row status changes only by a landed run.
