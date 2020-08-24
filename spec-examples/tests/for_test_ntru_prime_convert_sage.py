#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jun 25 15:43:27 2020

@author: baba
"""

def from_sage_to_hacspec_ntru_prime(x):
    #ADJUST, here you have to enter the right R class, eg. "*xp^" for R_p    
    r = x.split("*xqp^")
    if (int(r[1].split(" ")[0])+1) > 761:
        result = [0] * 858
    elif (int(r[1].split(" ")[0])+1) > 653:
        result = [0] * 762
    else :
        result = [0] * 654
    result[int(r[1].split(" ")[0])] = int(r[0])
    for i in range(1,len(r)-1):
        part = r[i].split(" ")
        sign = int(part[1] + "1")
        coeff = int(part[2])
        deg_2 = int(r[i+1].split(" ")[0])

        # i is odd and r[i] is something like r[i] =" 432 - 324"
        result[deg_2] = sign * coeff
    return "Seq::from_native_slice(&" + str(result) + ");"


# HERE input each print output, CAUTION you have to make small manipulation of the string, eg. 'xp - 2', must be '1*xp^1 - 2*xp^0'
print(from_sage_to_hacspec_ntru_prime("3471*xqp^856 + 4950*xqp^855 + 4040*xqp^854 + 2223*xqp^853 + 689*xqp^852 + 3287*xqp^851 + 2417*xqp^850 + 299*xqp^849 + 172*xqp^848 + 1507*xqp^847 + 2280*xqp^846 + 3022*xqp^845 + 4897*xqp^844 + 4510*xqp^843 + 1523*xqp^842 + 1756*xqp^841 + 699*xqp^840 + 2095*xqp^839 + 157*xqp^838 + 1173*xqp^837 + 369*xqp^836 + 1556*xqp^835 + 1106*xqp^834 + 1352*xqp^833 + 3526*xqp^832 + 2240*xqp^831 + 4130*xqp^830 + 519*xqp^829 + 4008*xqp^828 + 2119*xqp^827 + 3771*xqp^826 + 18*xqp^825 + 4634*xqp^824 + 2278*xqp^823 + 106*xqp^822 + 83*xqp^821 + 545*xqp^820 + 4688*xqp^819 + 1434*xqp^818 + 4601*xqp^817 + 4284*xqp^816 + 1225*xqp^815 + 174*xqp^814 + 1955*xqp^813 + 4746*xqp^812 + 4461*xqp^811 + 3392*xqp^810 + 3946*xqp^809 + 496*xqp^808 + 1898*xqp^807 + 952*xqp^806 + 1029*xqp^805 + 2731*xqp^804 + 3988*xqp^803 + 2657*xqp^802 + 4267*xqp^801 + 276*xqp^800 + 4646*xqp^799 + 4027*xqp^798 + 580*xqp^797 + 3908*xqp^796 + 223*xqp^795 + 3669*xqp^794 + 2170*xqp^793 + 5148*xqp^792 + 420*xqp^791 + 3105*xqp^790 + 3483*xqp^789 + 3237*xqp^788 + 2760*xqp^787 + 4633*xqp^786 + 2614*xqp^785 + 1779*xqp^784 + 4102*xqp^783 + 1226*xqp^782 + 4508*xqp^781 + 2180*xqp^780 + 2348*xqp^779 + 2224*xqp^778 + 2540*xqp^777 + 3459*xqp^776 + 722*xqp^775 + 655*xqp^774 + 4182*xqp^773 + 5061*xqp^772 + 3011*xqp^771 + 5056*xqp^770 + 1161*xqp^769 + 1105*xqp^768 + 3071*xqp^767 + 1687*xqp^766 + 796*xqp^765 + 1759*xqp^764 + 2923*xqp^763 + 2573*xqp^762 + 4022*xqp^761 + 2695*xqp^760 + 4966*xqp^759 + 2874*xqp^758 + 3171*xqp^757 + 4156*xqp^756 + 1094*xqp^755 + 3185*xqp^754 + 2748*xqp^753 + 1347*xqp^752 + 4389*xqp^751 + 2485*xqp^750 + 771*xqp^749 + 1755*xqp^748 + 307*xqp^747 + 1523*xqp^746 + 3983*xqp^745 + 1216*xqp^744 + 2344*xqp^743 + 1983*xqp^742 + 2575*xqp^741 + 4333*xqp^740 + 1427*xqp^739 + 2423*xqp^738 + 4396*xqp^737 + 234*xqp^736 + 714*xqp^735 + 3035*xqp^734 + 4784*xqp^733 + 2335*xqp^732 + 5163*xqp^731 + 4003*xqp^730 + 1643*xqp^729 + 3519*xqp^728 + 4166*xqp^727 + 666*xqp^726 + 1892*xqp^725 + 2479*xqp^724 + 3735*xqp^723 + 2465*xqp^722 + 4201*xqp^721 + 3425*xqp^720 + 2416*xqp^719 + 4454*xqp^718 + 1237*xqp^717 + 1725*xqp^716 + 929*xqp^715 + 1872*xqp^714 + 1316*xqp^713 + 3793*xqp^712 + 4811*xqp^711 + 3185*xqp^710 + 3962*xqp^709 + 4443*xqp^708 + 4106*xqp^707 + 3817*xqp^706 + 1181*xqp^705 + 1992*xqp^704 + 2*xqp^703 + 3718*xqp^702 + 1912*xqp^701 + 4644*xqp^700 + 2627*xqp^699 + 4843*xqp^698 + 377*xqp^697 + 1297*xqp^696 + 715*xqp^695 + 4492*xqp^694 + 1960*xqp^693 + 2713*xqp^692 + 4312*xqp^691 + 4009*xqp^690 + 3502*xqp^689 + 2957*xqp^688 + 3401*xqp^687 + 4870*xqp^686 + 3295*xqp^685 + 1129*xqp^684 + 66*xqp^683 + 4115*xqp^682 + 2681*xqp^681 + 4788*xqp^680 + 4319*xqp^679 + 1894*xqp^678 + 3298*xqp^677 + 4387*xqp^676 + 249*xqp^675 + 4485*xqp^674 + 4356*xqp^673 + 3482*xqp^672 + 768*xqp^671 + 210*xqp^670 + 575*xqp^669 + 4794*xqp^668 + 2229*xqp^667 + 846*xqp^666 + 1433*xqp^665 + 2751*xqp^664 + 3342*xqp^663 + 4944*xqp^662 + 3756*xqp^661 + 2267*xqp^660 + 530*xqp^659 + 4278*xqp^658 + 285*xqp^657 + 1008*xqp^656 + 984*xqp^655 + 1388*xqp^654 + 466*xqp^653 + 184*xqp^652 + 624*xqp^651 + 4308*xqp^650 + 3969*xqp^649 + 1710*xqp^648 + 4630*xqp^647 + 4982*xqp^646 + 3497*xqp^645 + 4468*xqp^644 + 1398*xqp^643 + 3502*xqp^642 + 1154*xqp^641 + 1641*xqp^640 + 1362*xqp^639 + 424*xqp^638 + 272*xqp^637 + 4475*xqp^636 + 533*xqp^635 + 4991*xqp^634 + 2701*xqp^633 + 238*xqp^632 + 867*xqp^631 + 2714*xqp^630 + 1816*xqp^629 + 4076*xqp^628 + 4270*xqp^627 + 533*xqp^626 + 717*xqp^625 + 1352*xqp^624 + 2972*xqp^623 + 4023*xqp^622 + 4339*xqp^621 + 3546*xqp^620 + 2210*xqp^619 + 1551*xqp^618 + 4659*xqp^617 + 3305*xqp^616 + 3961*xqp^615 + 3264*xqp^614 + 3528*xqp^613 + 4860*xqp^612 + 228*xqp^611 + 37*xqp^610 + 167*xqp^609 + 381*xqp^608 + 3146*xqp^607 + 2621*xqp^606 + 3840*xqp^605 + 3660*xqp^604 + 2089*xqp^603 + 1531*xqp^602 + 1*xqp^601 + 3097*xqp^600 + 549*xqp^599 + 4357*xqp^598 + 2533*xqp^597 + 2009*xqp^596 + 1918*xqp^595 + 3569*xqp^594 + 4831*xqp^593 + 3222*xqp^592 + 1629*xqp^591 + 2761*xqp^590 + 1220*xqp^589 + 641*xqp^588 + 4158*xqp^587 + 3389*xqp^586 + 2331*xqp^585 + 1919*xqp^584 + 3446*xqp^583 + 4028*xqp^582 + 3400*xqp^581 + 5023*xqp^580 + 415*xqp^579 + 1850*xqp^578 + 461*xqp^577 + 4528*xqp^576 + 23*xqp^575 + 3031*xqp^574 + 1189*xqp^573 + 907*xqp^572 + 1138*xqp^571 + 1586*xqp^570 + 3433*xqp^569 + 3992*xqp^568 + 4287*xqp^567 + 3666*xqp^566 + 4339*xqp^565 + 3160*xqp^564 + 568*xqp^563 + 433*xqp^562 + 2723*xqp^561 + 3597*xqp^560 + 904*xqp^559 + 1741*xqp^558 + 4017*xqp^557 + 4381*xqp^556 + 920*xqp^555 + 406*xqp^554 + 870*xqp^553 + 2342*xqp^552 + 4651*xqp^551 + 1152*xqp^550 + 2090*xqp^549 + 2676*xqp^548 + 457*xqp^547 + 184*xqp^546 + 3296*xqp^545 + 2496*xqp^544 + 4579*xqp^543 + 5052*xqp^542 + 3953*xqp^541 + 2358*xqp^540 + 4660*xqp^539 + 2291*xqp^538 + 98*xqp^537 + 2464*xqp^536 + 3065*xqp^535 + 1244*xqp^534 + 3857*xqp^533 + 3641*xqp^532 + 264*xqp^531 + 4464*xqp^530 + 335*xqp^529 + 129*xqp^528 + 148*xqp^527 + 3720*xqp^526 + 1027*xqp^525 + 3002*xqp^524 + 3537*xqp^523 + 1460*xqp^522 + 578*xqp^521 + 4274*xqp^520 + 68*xqp^519 + 2072*xqp^518 + 3372*xqp^517 + 2741*xqp^516 + 1217*xqp^515 + 4066*xqp^514 + 4394*xqp^513 + 316*xqp^512 + 421*xqp^511 + 2956*xqp^510 + 36*xqp^509 + 1007*xqp^508 + 2565*xqp^507 + 4456*xqp^506 + 3866*xqp^505 + 1200*xqp^504 + 4480*xqp^503 + 2383*xqp^502 + 469*xqp^501 + 2491*xqp^500 + 2023*xqp^499 + 1755*xqp^498 + 4802*xqp^497 + 2606*xqp^496 + 2852*xqp^495 + 2982*xqp^494 + 1901*xqp^493 + 5155*xqp^492 + 537*xqp^491 + 2867*xqp^490 + 691*xqp^489 + 2809*xqp^488 + 2833*xqp^487 + 2675*xqp^486 + 664*xqp^485 + 4054*xqp^484 + 3867*xqp^483 + 905*xqp^482 + 2552*xqp^481 + 3180*xqp^480 + 3223*xqp^479 + 4453*xqp^478 + 2026*xqp^477 + 3940*xqp^476 + 1022*xqp^475 + 4130*xqp^474 + 2432*xqp^473 + 3491*xqp^472 + 4480*xqp^471 + 4141*xqp^470 + 3013*xqp^469 + 1241*xqp^468 + 807*xqp^467 + 2326*xqp^466 + 2480*xqp^465 + 1746*xqp^464 + 3616*xqp^463 + 252*xqp^462 + 4916*xqp^461 + 821*xqp^460 + 4369*xqp^459 + 3951*xqp^458 + 883*xqp^457 + 4697*xqp^456 + 966*xqp^455 + 22*xqp^454 + 1643*xqp^453 + 1783*xqp^452 + 3898*xqp^451 + 4947*xqp^450 + 4613*xqp^449 + 805*xqp^448 + 2516*xqp^447 + 4097*xqp^446 + 4579*xqp^445 + 3305*xqp^444 + 4483*xqp^443 + 1764*xqp^442 + 2964*xqp^441 + 77*xqp^440 + 175*xqp^439 + 103*xqp^438 + 4639*xqp^437 + 3347*xqp^436 + 4645*xqp^435 + 4451*xqp^434 + 3697*xqp^433 + 1890*xqp^432 + 2163*xqp^431 + 1298*xqp^430 + 860*xqp^429 + 476*xqp^428 + 1715*xqp^427 + 3625*xqp^426 + 66*xqp^425 + 764*xqp^424 + 2354*xqp^423 + 3795*xqp^422 + 1374*xqp^421 + 2730*xqp^420 + 1737*xqp^419 + 471*xqp^418 + 99*xqp^417 + 1133*xqp^416 + 3973*xqp^415 + 3143*xqp^414 + 630*xqp^413 + 214*xqp^412 + 3368*xqp^411 + 3697*xqp^410 + 2072*xqp^409 + 3318*xqp^408 + 4263*xqp^407 + 666*xqp^406 + 310*xqp^405 + 3779*xqp^404 + 4191*xqp^403 + 4671*xqp^402 + 2926*xqp^401 + 4265*xqp^400 + 3387*xqp^399 + 4718*xqp^398 + 1574*xqp^397 + 367*xqp^396 + 2375*xqp^395 + 975*xqp^394 + 1778*xqp^393 + 4944*xqp^392 + 4580*xqp^391 + 3769*xqp^390 + 4*xqp^389 + 3808*xqp^388 + 2485*xqp^387 + 347*xqp^386 + 444*xqp^385 + 4042*xqp^384 + 3875*xqp^383 + 1049*xqp^382 + 2077*xqp^381 + 372*xqp^380 + 1148*xqp^379 + 1195*xqp^378 + 748*xqp^377 + 4224*xqp^376 + 1007*xqp^375 + 2879*xqp^374 + 4416*xqp^373 + 2800*xqp^372 + 3634*xqp^371 + 3829*xqp^370 + 4653*xqp^369 + 794*xqp^368 + 4794*xqp^367 + 2446*xqp^366 + 3373*xqp^365 + 508*xqp^364 + 2275*xqp^363 + 741*xqp^362 + 2975*xqp^361 + 238*xqp^360 + 2361*xqp^359 + 4822*xqp^358 + 1902*xqp^357 + 3506*xqp^356 + 3291*xqp^355 + 1269*xqp^354 + 2773*xqp^353 + 3560*xqp^352 + 2555*xqp^351 + 2233*xqp^350 + 1352*xqp^349 + 3720*xqp^348 + 3770*xqp^347 + 2137*xqp^346 + 1087*xqp^345 + 2964*xqp^344 + 3324*xqp^343 + 4649*xqp^342 + 3684*xqp^341 + 4330*xqp^340 + 102*xqp^339 + 3384*xqp^338 + 4300*xqp^337 + 3202*xqp^336 + 1048*xqp^335 + 3711*xqp^334 + 1572*xqp^333 + 2184*xqp^332 + 3929*xqp^331 + 3800*xqp^330 + 851*xqp^329 + 509*xqp^328 + 966*xqp^327 + 2947*xqp^326 + 2149*xqp^325 + 236*xqp^324 + 3816*xqp^323 + 1895*xqp^322 + 2535*xqp^321 + 1796*xqp^320 + 62*xqp^319 + 2564*xqp^318 + 4897*xqp^317 + 1279*xqp^316 + 4783*xqp^315 + 4595*xqp^314 + 3243*xqp^313 + 4589*xqp^312 + 2635*xqp^311 + 3897*xqp^310 + 3980*xqp^309 + 5055*xqp^308 + 3116*xqp^307 + 1760*xqp^306 + 521*xqp^305 + 2080*xqp^304 + 1322*xqp^303 + 4620*xqp^302 + 2333*xqp^301 + 3539*xqp^300 + 4797*xqp^299 + 4960*xqp^298 + 2068*xqp^297 + 3680*xqp^296 + 3053*xqp^295 + 2119*xqp^294 + 2498*xqp^293 + 1821*xqp^292 + 2487*xqp^291 + 4624*xqp^290 + 939*xqp^289 + 3355*xqp^288 + 1716*xqp^287 + 3095*xqp^286 + 349*xqp^285 + 2102*xqp^284 + 5018*xqp^283 + 4328*xqp^282 + 1243*xqp^281 + 1017*xqp^280 + 493*xqp^279 + 4411*xqp^278 + 2331*xqp^277 + 3312*xqp^276 + 1767*xqp^275 + 1397*xqp^274 + 4407*xqp^273 + 2972*xqp^272 + 3274*xqp^271 + 3002*xqp^270 + 3435*xqp^269 + 1467*xqp^268 + 1289*xqp^267 + 1073*xqp^266 + 2196*xqp^265 + 3502*xqp^264 + 1842*xqp^263 + 4552*xqp^262 + 4998*xqp^261 + 4496*xqp^260 + 490*xqp^259 + 3779*xqp^258 + 2894*xqp^257 + 5033*xqp^256 + 3703*xqp^255 + 5078*xqp^254 + 2474*xqp^253 + 3315*xqp^252 + 2498*xqp^251 + 2260*xqp^250 + 3367*xqp^249 + 1088*xqp^248 + 2208*xqp^247 + 4861*xqp^246 + 3303*xqp^245 + 4072*xqp^244 + 4879*xqp^243 + 2960*xqp^242 + 5124*xqp^241 + 3517*xqp^240 + 4773*xqp^239 + 4011*xqp^238 + 4042*xqp^237 + 4843*xqp^236 + 4712*xqp^235 + 3581*xqp^234 + 171*xqp^233 + 4792*xqp^232 + 1923*xqp^231 + 1606*xqp^230 + 4417*xqp^229 + 1557*xqp^228 + 2993*xqp^227 + 149*xqp^226 + 2918*xqp^225 + 1839*xqp^224 + 2185*xqp^223 + 3752*xqp^222 + 2096*xqp^221 + 4448*xqp^220 + 2965*xqp^219 + 1647*xqp^218 + 805*xqp^217 + 3587*xqp^216 + 189*xqp^215 + 527*xqp^214 + 489*xqp^213 + 3236*xqp^212 + 92*xqp^211 + 3646*xqp^210 + 5029*xqp^209 + 36*xqp^208 + 2768*xqp^207 + 4309*xqp^206 + 869*xqp^205 + 1638*xqp^204 + 3161*xqp^203 + 1258*xqp^202 + 525*xqp^201 + 1496*xqp^200 + 2880*xqp^199 + 1034*xqp^198 + 4876*xqp^197 + 354*xqp^196 + 2407*xqp^195 + 3966*xqp^194 + 1304*xqp^193 + 3658*xqp^192 + 4142*xqp^191 + 1871*xqp^190 + 1036*xqp^189 + 3479*xqp^188 + 4353*xqp^187 + 1909*xqp^186 + 5141*xqp^185 + 3146*xqp^184 + 968*xqp^183 + 1241*xqp^182 + 2351*xqp^181 + 962*xqp^180 + 4705*xqp^179 + 3222*xqp^178 + 4503*xqp^177 + 3525*xqp^176 + 4751*xqp^175 + 66*xqp^174 + 2115*xqp^173 + 3816*xqp^172 + 2349*xqp^171 + 4836*xqp^170 + 2846*xqp^169 + 980*xqp^168 + 1996*xqp^167 + 4628*xqp^166 + 3521*xqp^165 + 1174*xqp^164 + 2786*xqp^163 + 1783*xqp^162 + 2825*xqp^161 + 1038*xqp^160 + 835*xqp^159 + 3616*xqp^158 + 5051*xqp^157 + 4936*xqp^156 + 683*xqp^155 + 1105*xqp^154 + 995*xqp^153 + 2634*xqp^152 + 3884*xqp^151 + 4622*xqp^150 + 3175*xqp^149 + 650*xqp^148 + 2291*xqp^147 + 2999*xqp^146 + 148*xqp^145 + 3527*xqp^144 + 928*xqp^143 + 3345*xqp^142 + 3757*xqp^141 + 1274*xqp^140 + 5127*xqp^139 + 2482*xqp^138 + 4563*xqp^137 + 3859*xqp^136 + 2719*xqp^135 + 3418*xqp^134 + 2350*xqp^133 + 965*xqp^132 + 4456*xqp^131 + 1560*xqp^130 + 4168*xqp^129 + 2242*xqp^128 + 457*xqp^127 + 3565*xqp^126 + 1855*xqp^125 + 4246*xqp^124 + 4965*xqp^123 + 449*xqp^122 + 2234*xqp^121 + 3134*xqp^120 + 2228*xqp^119 + 4823*xqp^118 + 182*xqp^117 + 4610*xqp^116 + 4962*xqp^115 + 4650*xqp^114 + 2959*xqp^113 + 2041*xqp^112 + 1026*xqp^111 + 1715*xqp^110 + 3814*xqp^109 + 1186*xqp^108 + 4742*xqp^107 + 2833*xqp^106 + 2200*xqp^105 + 2539*xqp^104 + 307*xqp^103 + 478*xqp^102 + 284*xqp^101 + 2486*xqp^100 + 4002*xqp^99 + 2331*xqp^98 + 4210*xqp^97 + 3415*xqp^96 + 3967*xqp^95 + 264*xqp^94 + 516*xqp^93 + 262*xqp^92 + 1808*xqp^91 + 1044*xqp^90 + 3686*xqp^89 + 1509*xqp^88 + 4499*xqp^87 + 367*xqp^86 + 3873*xqp^85 + 1058*xqp^84 + 5032*xqp^83 + 5099*xqp^82 + 814*xqp^81 + 4784*xqp^80 + 5147*xqp^79 + 2362*xqp^78 + 2226*xqp^77 + 4290*xqp^76 + 3925*xqp^75 + 553*xqp^74 + 3887*xqp^73 + 586*xqp^72 + 4142*xqp^71 + 4186*xqp^70 + 1070*xqp^69 + 4295*xqp^68 + 4848*xqp^67 + 2322*xqp^66 + 4724*xqp^65 + 2591*xqp^64 + 3982*xqp^63 + 1238*xqp^62 + 4751*xqp^61 + 703*xqp^60 + 4701*xqp^59 + 2170*xqp^58 + 1455*xqp^57 + 2342*xqp^56 + 1934*xqp^55 + 4923*xqp^54 + 2668*xqp^53 + 1993*xqp^52 + 5076*xqp^51 + 985*xqp^50 + 4769*xqp^49 + 2957*xqp^48 + 1670*xqp^47 + 3307*xqp^46 + 927*xqp^45 + 1497*xqp^44 + 2515*xqp^43 + 3927*xqp^42 + 4635*xqp^41 + 5085*xqp^40 + 1048*xqp^39 + 1298*xqp^38 + 145*xqp^37 + 1795*xqp^36 + 5016*xqp^35 + 3763*xqp^34 + 5111*xqp^33 + 4623*xqp^32 + 602*xqp^31 + 1923*xqp^30 + 5097*xqp^29 + 3428*xqp^28 + 1808*xqp^27 + 1596*xqp^26 + 3355*xqp^25 + 1801*xqp^24 + 1117*xqp^23 + 4947*xqp^22 + 1967*xqp^21 + 2200*xqp^20 + 5110*xqp^19 + 2845*xqp^18 + 3826*xqp^17 + 1671*xqp^16 + 2762*xqp^15 + 1611*xqp^14 + 1795*xqp^13 + 4101*xqp^12 + 4858*xqp^11 + 3191*xqp^10 + 353*xqp^9 + 3879*xqp^8 + 4100*xqp^7 + 5021*xqp^6 + 2357*xqp^5 + 3523*xqp^4 + 4742*xqp^3 + 1727*xqp^2 + 3175*xqp + 4712"))
