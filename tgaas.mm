$[ set.mm $]

$( Extension of `set.mm` proving the exterior-angle theorem `tgexta2` and the
   AAS triangle congruence criterion `tgaas` in Tarski geometry.

   Every theorem here is a dependency of `tgaas`, and each is stated in its own
   block so that its `$e` hypotheses stay local.  The order is bottom-up:
   elementary consequences of triangle non-collinearity, the two
   degenerate-angle congruence constructors `set.mm` lacks, in-angle transport
   across an angle congruence, the exterior-angle theorem and its strictness
   half, and finally the AAS assembly, with `tgaas` the last `$p`.

   Strictness of an angle comparison has no primitive here: `set.mm` defines
   `leA` but no `ltA`, so "strictly less" is carried inline as `leA` together
   with the failure of `cgrA`. $)

$( Consequences of triangle non-collinearity: vertex inequalities, the
   dimension condition, and non-collinearity transported across an angle
   congruence. $)


${
  tgacne.p $e |- P = ( Base ` G ) $.
  tgacne.i $e |- I = ( Itv ` G ) $.
  tgacne.l $e |- L = ( LineG ` G ) $.
  tgacne.g $e |- ( ph -> G e. TarskiG ) $.
  tgacne.a $e |- ( ph -> A e. P ) $.
  tgacne.b $e |- ( ph -> B e. P ) $.
  tgacne.c $e |- ( ph -> C e. P ) $.
  tgacne.ncol $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.

  $( Non-collinearity of triangle `ABC` implies distinct vertices `A` and `C`. $)
  tgacne $p
    |- ( ph -> A =/= C )
      $= ( ncolrot1 ncolcom ncolne1 ) AEFGHBDCIJKLMONAEFGHCDBIKJLNOMAEFGHBCDIK
         JLMNOPQRS $.
$}

${
  tgbcne.p $e |- P = ( Base ` G ) $.
  tgbcne.i $e |- I = ( Itv ` G ) $.
  tgbcne.l $e |- L = ( LineG ` G ) $.
  tgbcne.g $e |- ( ph -> G e. TarskiG ) $.
  tgbcne.a $e |- ( ph -> A e. P ) $.
  tgbcne.b $e |- ( ph -> B e. P ) $.
  tgbcne.c $e |- ( ph -> C e. P ) $.
  tgbcne.ncol $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.

  $( Non-collinearity of triangle `ABC` implies distinct vertices `B` and `C`. $)
  tgbcne $p
    |- ( ph -> B =/= C )
      $= ( ncolrot2 ncolne1 ) AEFGHCDBIJKLNOMAEFGHBCDIKJLMNOPQR $.
$}

${
  tgatgdim2.p $e |- P = ( Base ` G ) $.
  tgatgdim2.l $e |- L = ( LineG ` G ) $.
  tgatgdim2.i $e |- I = ( Itv ` G ) $.
  tgatgdim2.g $e |- ( ph -> G e. TarskiG ) $.
  tgatgdim2.a $e |- ( ph -> A e. P ) $.
  tgatgdim2.b $e |- ( ph -> B e. P ) $.
  tgatgdim2.c $e |- ( ph -> C e. P ) $.
  tgatgdim2.ncol $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.

  $( Non-collinearity of triangle `ABC` supplies the dimension-2 condition. $)
  tgatgdim2 $p
    |- ( ph -> G TarskiGDim>= 2 )
      $= ( ncoltgdim2 ) AEFGHBCDIJKLMNOPQ $.
$}

${
  tgdefncol.p $e |- P = ( Base ` G ) $.
  tgdefncol.m $e |- .- = ( dist ` G ) $.
  tgdefncol.i $e |- I = ( Itv ` G ) $.
  tgdefncol.l $e |- L = ( LineG ` G ) $.
  tgdefncol.g $e |- ( ph -> G e. TarskiG ) $.
  tgdefncol.a $e |- ( ph -> A e. P ) $.
  tgdefncol.b $e |- ( ph -> B e. P ) $.
  tgdefncol.c $e |- ( ph -> C e. P ) $.
  tgdefncol.d $e |- ( ph -> D e. P ) $.
  tgdefncol.e $e |- ( ph -> E e. P ) $.
  tgdefncol.f $e |- ( ph -> F e. P ) $.
  tgdefncol.ncol $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.
  tgdefncol.cgra $e
    |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> ) $.

  $( Angle congruence transports source non-collinearity from `ABC` to `DEF`. $)
  tgdefncol $p
    |- ( ph -> -. ( F e. ( D L E ) \/ D = E ) )
      $= ( cgrancol ) ABCDEFGHIJKLMONQRSTUAUBUCUEPUDUF $.
$}

$( The two degenerate-angle congruence constructors `set.mm` lacks.  Every
   existing theorem concluding `cgrA` either copies an angle onto a
   non-collinear frame ( ~ acopy , ~ trgcopy ), moves along a ray from an
   angle already in hand ( ~ cgrahl1 , ~ cgrahl2 ), or is reflexivity,
   symmetry or transitivity.  Nothing builds a congruence between two
   degenerate angles out of their degeneracy alone, which is what the
   degenerate branches of in-angle transport need. $)

${
  $d x ph $. $d x A $. $d x B $. $d x C $. $d x D $. $d x E $. $d x F $.
  $d x G $. $d x P $. $d x I $. $d x K $. $d x .- $.
  $d y ph $. $d y A $. $d y B $. $d y C $. $d y D $. $d y E $. $d y F $.
  $d y G $. $d y P $. $d y I $. $d y K $. $d y .- $.
  $d x y $.
  cgrahlb.p $e |- P = ( Base ` G ) $.
  cgrahlb.i $e |- I = ( Itv ` G ) $.
  cgrahlb.k $e |- K = ( hlG ` G ) $.
  cgrahlb.m $e |- .- = ( dist ` G ) $.
  cgrahlb.g $e |- ( ph -> G e. TarskiG ) $.
  cgrahlb.a $e |- ( ph -> A e. P ) $.
  cgrahlb.b $e |- ( ph -> B e. P ) $.
  cgrahlb.c $e |- ( ph -> C e. P ) $.
  cgrahlb.d $e |- ( ph -> D e. P ) $.
  cgrahlb.e $e |- ( ph -> E e. P ) $.
  cgrahlb.f $e |- ( ph -> F e. P ) $.
  cgrahlb.1 $e |- ( ph -> A ( K ` B ) C ) $.
  cgrahlb.2 $e |- ( ph -> D ( K ` E ) F ) $.
  $( Two null angles are congruent: if `A` and `C` lie on one half-line from
     `B`, and `D` and `F` on one half-line from `E`, then angle `<" A B C ">`
     is congruent to `<" D E F ">`.  This is GeoCoq `l11_21_b`; `set.mm` has
     only the converse, ~ cgrahl (GeoCoq `l11_21_a`).  Proved by copying both
     arms onto the target rays with ~ hlcgrex and closing the third side by
     segment subtraction ( ~ tgcgrsub2 ), so it needs no non-collinear frame. $)
  cgrahlb $p |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )
      $= ( vx cv cfv wbr co wceq wa vy cs3 ccgra wcel cstrkg simplll syl
        simpllr simplr ccgrg eqid simpr simpld simprd eqcomd tgcgrcomlr cleg
        wne wo w3a ishlg mpbid simp3d hltr hlcomd tgcgrsub2 trgcgr iscgrad
        wrex hlne1 necomd hlcgrex hlne2 jca reeanv sylibr r19.29vva )
         AUFUGZEGKUHZUIZGWJLUJZCBLUJZUKZULZUMUGZHWKUIZGWQLUJZCDLUJZUKZULZULZBC
         DUNEGHUNIUOUHUIUFUMFFAWJFUPZULZWQFUPZULZXCULZBCDEFGHIJKWJWQMNOXHAIUQU
         PZAXDXFXCURZQUSZXHABFUPZXJRUSZXHACFUPZXJSUSZXHADFUPZXJTUSZXHAEFUPZXJU
         AUSZXHAGFUPZXJUBUSZXHAHFUPZXJUCUSZAXDXFXCUTZXEXFXCVAZXHBCDWJFIVBUHZGW
         QILMPYFVCXKXMXOXQYDYAYEXHCBGWJFIJLMPNXKXOXMYAYDXHWMWNXHWLWOXHWPXBXGXC
         VDZVEZVFZVGZVHXHWSWTXHWRXAXHWPXBYGVFZVFZVGZXHBDWJWQFIJLMPNXKXMXQYDYEX
         HCBDGFWJWQIJIVIUHZLMPNYNVCXKXOXMXQYAYAYDYEXHBCVJZDCVJZBCDJUJZUPZDCBJU
         JZUPZVKZXHBDCKUHZUIZYOYPUUAVLXHAUUCXJUDUSXHBDCFIJKUQMNOXMXQXOXKVMVNVO
         XHWJGVJZWQGVJZWJGWQJUJZUPZWQGWJJUJZUPZVKZXHWJWQWKUIUUDUUEUUJVLXHWJHWQ
         GFIJKMNOYDYCYEXKYAXHWJEHGFIJKMNOYDXSYCXKYAXHWLWOYHVEZXHAEHWKUIXJUEUSV
         PXHWQHGFIJKUQMNOYEYCYAXKXHWRXAYKVEZVQVPXHWJWQGFIJKUQMNOYDYEYAXKVMVNVO
         YJYMVRVHVSUUKUULVTAWPUFFWAZXBUMFWAZULXCUMFWAUFFWAAUUMUUNAUFGCBEFIJKLM
         NOUBSRQUAPAEHGFIJKUQMNOUAUCUBQUEWBABCABDCFIJKUQMNORTSQUDWBWCWDAUMGCDH
         FIJKLMNOUBSTQUCPAEHGFIJKUQMNOUAUCUBQUEWEADCABDCFIJKUQMNORTSQUDWEWCWDW
         FWPXBUFUMFFWGWHWI $.
$}

${
  $d x ph $. $d x A $. $d x B $. $d x C $. $d x D $. $d x E $. $d x F $.
  $d x G $. $d x P $. $d x I $. $d x K $. $d x .- $.
  $d y ph $. $d y A $. $d y B $. $d y C $. $d y D $. $d y E $. $d y F $.
  $d y G $. $d y P $. $d y I $. $d y K $. $d y .- $.
  $d x y $.
  cgrabtwnb.p $e |- P = ( Base ` G ) $.
  cgrabtwnb.i $e |- I = ( Itv ` G ) $.
  cgrabtwnb.k $e |- K = ( hlG ` G ) $.
  cgrabtwnb.m $e |- .- = ( dist ` G ) $.
  cgrabtwnb.g $e |- ( ph -> G e. TarskiG ) $.
  cgrabtwnb.a $e |- ( ph -> A e. P ) $.
  cgrabtwnb.b $e |- ( ph -> B e. P ) $.
  cgrabtwnb.c $e |- ( ph -> C e. P ) $.
  cgrabtwnb.d $e |- ( ph -> D e. P ) $.
  cgrabtwnb.e $e |- ( ph -> E e. P ) $.
  cgrabtwnb.f $e |- ( ph -> F e. P ) $.
  cgrabtwnb.1 $e |- ( ph -> B e. ( A I C ) ) $.
  cgrabtwnb.2 $e |- ( ph -> E e. ( D I F ) ) $.
  cgrabtwnb.3 $e |- ( ph -> A =/= B ) $.
  cgrabtwnb.4 $e |- ( ph -> C =/= B ) $.
  cgrabtwnb.5 $e |- ( ph -> D =/= E ) $.
  cgrabtwnb.6 $e |- ( ph -> F =/= E ) $.
  $( Two flat angles are congruent: if `B` lies strictly between `A` and `C`,
     and `E` strictly between `D` and `F`, then angle `<" A B C ">` is
     congruent to `<" D E F ">`.  This is the converse of ~ cgrabtwn .  The
     four distinctness hypotheses are required: `cgrA` is non-degenerate at
     the vertex ( ~ cgrane1 through ~ cgrane4 ), and betweenness alone permits
     a collapsed arm.  Same skeleton as ~ cgrahlb with segment addition
     ( ~ tgcgrextend ) in place of subtraction. $)
  cgrabtwnb $p |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> )
      $= ( vx cv cfv wbr co wceq wa vy cs3 ccgra wcel cstrkg simplll syl
        simpllr simplr ccgrg eqid simpr simpld simprd tgcgrcomlr eqcomd hlcomd
        btwnhl tgbtwncom tgcgrextend trgcgr iscgrad wrex necomd hlcgrex jca
        reeanv sylibr r19.29vva ) AUJUKZEGKULZUMZGWFLUNZCBLUNZUOZUPZUQUKZHWGUM
         ZGWMLUNZCDLUNZUOZUPZUPZBCDUREGHURIUSULUMUJUQFFAWFFUTZUPZWMFUTZUPZWSUP
         ZBCDEFGHIJKWFWMMNOXDAIVAUTZAWTXBWSVBZQVCZXDABFUTZXFRVCZXDACFUTZXFSVCZ
         XDADFUTZXFTVCZXDAEFUTZXFUAVCZXDAGFUTZXFUBVCZXDAHFUTZXFUCVCZAWTXBWSVDZ
         XAXBWSVEZXDBCDWFFIVFULZGWMILMPYBVGXGXIXKXMXTXQYAXDWFGLUNZBCLUNZXDGWFC
         BFIJLMPNXGXQXTXKXIXDWHWKXDWLWRXCWSVHZVIZVJZVKZVLZXDWOWPXDWNWQXDWLWRYE
         VJZVJZVLZXDBDWFWMFIJLMPNXGXIXMXTYAXDBCDWFFGWMIJLMPNXGXIXKXMXTXQYAXDAC
         BDJUNUTXFUDVCXDWMGWFFIJLMPNXGYAXQXTXDHWMWFGFIJKMNOXSYAXTXGXQXDWMHGFIJ
         KVAMNOYAXSXQXGXDWNWQYJVIZVMXDWFGHFIJLMPNXGXTXQXSXDEWFHGFIJKMNOXOXTXSX
         GXQXDWFEGFIJKVAMNOXTXOXQXGXDWHWKYFVIZVMXDAGEHJUNUTXFUEVCVNVOVNVOYIYLV
         PVKVQYNYMVRAWLUJFVSZWRUQFVSZUPWSUQFVSUJFVSAYOYPAUJGCBEFIJKLMNOUBSRQUA
         PUHABCUFVTWAAUQGCDHFIJKLMNOUBSTQUCPUIADCUGVTWAWBWLWRUJUQFFWCWDWE $.
$}

${
  $d x ph $. $d x P $. $d x I $. $d x K $. $d x G $.
  $d x D $. $d x E $. $d x F $. $d x W $. $d x .- $.
  iabt.p $e |- P = ( Base ` G ) $.
  iabt.i $e |- I = ( Itv ` G ) $.
  iabt.k $e |- K = ( hlG ` G ) $.
  iabt.g $e |- ( ph -> G e. TarskiG ) $.
  iabt.d $e |- ( ph -> D e. P ) $.
  iabt.e $e |- ( ph -> E e. P ) $.
  iabt.f $e |- ( ph -> F e. P ) $.
  iabt.w $e |- ( ph -> W e. P ) $.
  iabt.in $e |- ( ph -> W ( inA ` G ) <" D E F "> ) $.
  iabt.1 $e |- ( ph -> E e. ( D I W ) ) $.
  $( A flat sub-angle forces the containing angle flat: if `W` is inside angle
     `<" D E F ">` and `E` lies between `D` and `W`, then `E` lies between `D`
     and `F`.  This is GeoCoq `bet_in_angle_bet`; a label sweep over the
     `inag*` family found no `set.mm` counterpart.  Proved by unfolding
     ~ isinag and following its segment point. $)
  inagbtwn $p |- ( ph -> E e. ( D I F ) )
      $= ( vx cv co wcel wceq cfv wbr wo wa simpl simpr simpld syl eleq1d
        mpbid cds eqid cstrkg simpll simplr tgbtwnintr tgbtwncom wne w3a ishlg
        simp2d necomd tgbtwnouttr simp3d mpjaodan tgbtwnexch simprd wrex cs3
        cinag isinag r19.29a ) ATUAZBEGUBZUCZVQDUDZVQIDHUEZUFZUGZUHZDVRUCZTCAV
         QCUCZUHZWDUHZVTWEWBWHVTUHZVSWEWIWHVSWHVTUIWHVSWCWGWDUJZUKZULWIVQDVRWH
         VTUJUMUNWHWBUHZBDVQECFGFUOUEZJWMUPZKWLWHFUQUCZWHWBUIZWHAWOAWFWDURZMUL
         ZULZWLWHBCUCZWPWHAWTWQNULZULZWLWHDCUCZWPWHAXCWQOULZULZWLWHWFWPAWFWDUS
         ZULZWLWHECUCZWPWHAXHWQPULULWLVQDIGUBZUCZDBVQGUBUCIDVQGUBZUCZWLXJUHZVQ
         DBCFGWMJWNKXMWLWOWLXJUIZWSULZXMWLWFXNXGULZXMWLXCXNXEULZXMWLWTXNXBULZX
         MVQDBICFGWMJWNKXOXPXQXRXMWLICUCZXNWLWHXSWPWHAXSWQQULZULZULWLXJUJXMWLD
         BIGUBZUCZXNWLWHYCWPWHAYCWQSULZULZULUTVAWLXLUHZBDIVQCFGWMJWNKYFWLWOWLX
         LUIZWSULYFWLWTYGXBULYFWLXCYGXEULYFWLXSYGYAULYFWLWFYGXGULYFWLDIVBYGWLI
         DWLVQDVBZIDVBZXJXLUGZWLWBYHYIYJVCZWHWBUJZWLVQIDCFGHUQJKLXGYAXEWSVDZUN
         ZVEVFULYFWLYCYGYEULWLXLUJVGWLYHYIYJYNVHVIWLWHVSWPWKULVJWHVSWCWJVKVIAB
         DVBZEDVBZYIVCZWDTCVLZAIBDEVMFVNUEUFYQYRUHRATBDECFGHUQIJKLQNOPMVOUNVKV
         P $.
$}

${
  $d v ph $. $d v P $. $d v I $. $d v K $. $d v G $.
  $d v D $. $d v E $. $d v F $. $d v W $.
  $d v X $. $d v Y $. $d v Z $.
  iashl.p $e |- P = ( Base ` G ) $.
  iashl.i $e |- I = ( Itv ` G ) $.
  iashl.k $e |- K = ( hlG ` G ) $.
  iashl.g $e |- ( ph -> G e. TarskiG ) $.
  iashl.d $e |- ( ph -> D e. P ) $.
  iashl.e $e |- ( ph -> E e. P ) $.
  iashl.f $e |- ( ph -> F e. P ) $.
  iashl.w $e |- ( ph -> W e. P ) $.
  iashl.x $e |- ( ph -> X e. P ) $.
  iashl.y $e |- ( ph -> Y e. P ) $.
  iashl.z $e |- ( ph -> Z e. P ) $.
  iashl.cgb $e |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.
  iashl.1 $e |- ( ph -> D ( K ` E ) W ) $.
  $( In-angle transport, degenerate branch (i): the sub-angle `<" D E W ">` is
     **null**, `W` lying on ray `ED`.  The witness is not constructed -- it is
     `X`, the target's own first arm -- and ~ cgrahlb supplies the copied angle
     from the two ray degeneracies.  No GeoCoq counterpart: GeoCoq's branch only
     locates a witness supplied by its universal statement. $)
  inagcgrasubhl $p |- ( ph -> E. v e. P ( v ( inA ` G ) <" X Y Z "> /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( cv cs3 cinag cfv wbr ccgra wa wceq simpr breq1d eqidd s3eqd breq2d
        anbi12d cstrkg cgrane3 necomd cgrane4 cds eqid tgbtwntriv1 hlid olcd
        isinagd cgrahlb jca rspcedvd ) ABUGZKLMUHZGUIUJZUKZCEJUHZKLVNUHZGULUJZ
         UKZUMKVOVPUKZVRKLKUHZVTUKZUMBKDUBAVNKUNZUMZVQWBWAWDWFVNKVOVPAWEUOZUPW
         FVSWCVRVTWFKLVNKKLWFKUQWFLUQWGURUSUTAWBWDAKLMDGHIVAKKNOPUBUBUCUDQUBAL
         KACEFKDLMGHINOPQRSTUBUCUDUEVBZVCZALMACEFKDLMGHINOPQRSTUBUCUDUEVDVCWIA
         KMDGHGVEUJZNWJVFZOQUBUDVGAKKLIUJUKKLUNAKKLDGHINOPUBUBUCQWIVHZVIVJACEJ
         KDLKGHIWJNOPWKQRSUAUBUCUBUFWLVKVLVM $.
$}

${
  $d v ph $. $d v P $. $d v I $. $d v K $. $d v G $.
  $d v D $. $d v E $. $d v F $. $d v W $.
  $d v X $. $d v Y $. $d v Z $.
  iasbt.p $e |- P = ( Base ` G ) $.
  iasbt.i $e |- I = ( Itv ` G ) $.
  iasbt.k $e |- K = ( hlG ` G ) $.
  iasbt.g $e |- ( ph -> G e. TarskiG ) $.
  iasbt.d $e |- ( ph -> D e. P ) $.
  iasbt.e $e |- ( ph -> E e. P ) $.
  iasbt.f $e |- ( ph -> F e. P ) $.
  iasbt.w $e |- ( ph -> W e. P ) $.
  iasbt.x $e |- ( ph -> X e. P ) $.
  iasbt.y $e |- ( ph -> Y e. P ) $.
  iasbt.z $e |- ( ph -> Z e. P ) $.
  iasbt.in $e |- ( ph -> W ( inA ` G ) <" D E F "> ) $.
  iasbt.cgb $e |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.
  iasbt.1 $e |- ( ph -> E e. ( D I W ) ) $.
  $( In-angle transport, degenerate branch (ii): the sub-angle `<" D E W ">` is
     **flat**, `E` lying between `D` and `W`.  The witness is built beyond `Y` on
     the ray opposite `YX` with ~ axtgsegcon , and ~ cgrabtwnb supplies the
     copied angle from the two betweennesses.  The in-angle conjunct goes
     through ~ inagbtwn , which carries the flatness up to the containing angle,
     then ~ cgrabtwn across the congruence and ~ isinagd on the target. $)
  inagcgrasubbtwn $p |- ( ph -> E. v e. P ( v ( inA ` G ) <" X Y Z "> /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( cv co wcel cds cfv wceq wa cs3 cinag wbr ccgra cstrkg simplr simpll
        syl wne cgrane3 necomd cgrane4 eqid simpr simprd eqcomd tgcgrneq
        inagbtwn cgrabtwn eqidd orcd isinagd simpld inagne1 inagne3 cgrabtwnb
        jca axtgsegcon reximddv3 ) ALKBUHZHUIZUJZLWDGUKULZUIZKLWGUIZUMZUNZWDKL
         MUOZGUPULZUQZCEJUOZKLWDUOZGURULZUQZUNBDAWDDUJZUNZWKUNZWNWRXAKLMDGHIUS
         WDLNOPAWSWKUTZXAAKDUJZAWSWKVAZUBVBZXAALDUJZXDUCVBZXAAMDUJXDUDVBXAAGUS
         UJZXDQVBZXGXAAKLVCZXDALKACEFKDLMGHINOPQRSTUBUCUDUFVDZVEZVBZXAAMLVCXDA
         LMACEFKDLMGHINOPQRSTUBUCUDUFVFVEVBXALWDXAKLLWDDGHWGNWGVGZOXIXEXGXGXBX
         AWHWIXAWFWJWTWKVHZVIZVJZXMVKZVEZXAALKMHUIUJXDACEFKDLMGHWGNOXNQRSTUBUC
         UDUFACDEFGHIJNOPQRSTUAUEUGVLVMVBXALLUMLWDLIULUQXALVNVOVPXACEJKDLWDGHI
         WGNOPXNXIXAACDUJXDRVBXAAEDUJXDSVBXAAJDUJXDUAVBXEXGXBXAAECJHUIUJXDUGVB
         XAWFWJXOVQXAACEVCXDACEFDGHIJNOPUARSTQUEVRVBXAAJEVCXDACEFDGHIJNOPUARST
         QUEVSVBXMXSVTWAABKLDGHWGKLNXNOQUBUCUBUCWBWC $.
$}

${
  $d c ph $. $d c P $. $d c I $. $d c K $. $d c L $. $d c G $.
  $d c D $. $d c E $. $d c F $. $d c W $.
  $d c X $. $d c Y $. $d c Z $. $d c v $.
  $d v ph $. $d v P $. $d v I $. $d v K $. $d v L $. $d v G $.
  $d v D $. $d v E $. $d v F $. $d v W $.
  $d v X $. $d v Y $. $d v Z $.
  iabtw.p $e |- P = ( Base ` G ) $.
  iabtw.i $e |- I = ( Itv ` G ) $.
  iabtw.k $e |- K = ( hlG ` G ) $.
  iabtw.l $e |- L = ( LineG ` G ) $.
  iabtw.g $e |- ( ph -> G e. TarskiG ) $.
  iabtw.d $e |- ( ph -> D e. P ) $.
  iabtw.e $e |- ( ph -> E e. P ) $.
  iabtw.f $e |- ( ph -> F e. P ) $.
  iabtw.w $e |- ( ph -> W e. P ) $.
  iabtw.x $e |- ( ph -> X e. P ) $.
  iabtw.y $e |- ( ph -> Y e. P ) $.
  iabtw.z $e |- ( ph -> Z e. P ) $.
  iabtw.cgb $e |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.
  iabtw.1 $e |- ( ph -> E e. ( D I F ) ) $.
  iabtw.2 $e |- ( ph -> -. ( W e. ( D L E ) \/ D = E ) ) $.
  $( In-angle transport, degenerate branch (iii): the containing angle is
     **flat** while the sub-angle is not.  This is the `x = E` disjunct of
     ~ isinag , which the non-degenerate spine cannot reach.  Unlike branches
     (i) and (ii) the copied angle must be *constructed*: the congruence
     hypothesis relates `W` to nothing on the target side, and ~ acopy needs a
     point off line `XY` to pick a side, which the collinear `Z` cannot be.
     ~ tgatgdim2 takes the dimension from this branch's own non-collinearity and
     ~ tglowdim2ln produces that point.  Both ~ ncolrot1 rotations are
     load-bearing. $)
  inagcgrabtwn $p |- ( ph -> E. v e. P ( v ( inA ` G ) <" X Y Z "> /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( vc cv co wcel wn cs3 cinag cfv wbr ccgra wa wrex chpg cstrkg simplr
        simpll syl wne cgrane3 necomd cgrane4 simpr simpld cds eqid cgrabtwn
        wceq eqidd orcd isinagd jca wo ncolrot1 neneqd ioran sylibr acopy
        reximddv3 tgatgdim2 tglowdim2ln r19.29a ) AUJUKZLMJULZUMZUNZBUKZLMNUOZ
         GUPUQZURZCEKUOZLMWOUOZGUSUQZURZUTZBDVAUJDAWKDUMZUTZWNUTZXBWOWKWLGVBUQ
         ZUQZURZUTZXCBDXFWODUMZUTZXJUTZWRXBXMLMNDGHIVCWOMOPQXFXKXJVDZXMXFLDUMZ
         XFXKXJVEZXFAXOAXDWNVEZUDVFZVFZXMXFMDUMZXPXFAXTXQUEVFZVFZXMXFNDUMZXPXF
         AYCXQUFVFVFXMXFGVCUMZXPXFAYDXQSVFZVFZYBXMXFLMVGZXPXFAYGXQAMLACEFLDMNG
         HIOPQSTUAUBUDUEUFUGVHZVIZVFZVFXMXFNMVGZXPXFAYKXQAMNACEFLDMNGHIOPQSTUA
         UBUDUEUFUGVJVIVFVFXMMWOXMCEKLDMWOGHIOPQYFXMXFCDUMZXPXFAYLXQTVFZVFXMXF
         EDUMZXPXFAYNXQUAVFZVFXMXFKDUMZXPXFAYPXQUCVFZVFXSYBXNXMXBXIXLXJVKZVLZV
         JVIXMXFMLNHULZUMZXPXFAUUAXQACEFLDMNGHGVMUQZOPUUBVNZSTUAUBUDUEUFUGUHVO
         VFVFXMMMVPMWOMIUQURXMMVQVRVSYSVTXFCEKLDBMWKGHJUUBOPUUCYEYMYOYQXRYAAXD
         WNVDZRXFACEKJULUMEKVPWAUNXQADGHJCEKORPSTUAUCUIWBVFXFDGHJLMWKORPYEXRYA
         UUDXFWNLMVPZUNZUTWMUUEWAUNXFWNUUFXEWNVKXFLMYJWCVTWMUUEWDWEWBWFWGALMDG
         HJUJOPRSACEKDGHJORPSTUAUCUIWHUDUEYIWIWJ $.
$}

${
  $d x ph $. $d x P $. $d x I $. $d x K $. $d x G $. $d x .- $.
  $d x A $. $d x B $. $d x C $. $d x D $. $d x E $. $d x F $.
  $d y ph $. $d y P $. $d y I $. $d y K $. $d y G $. $d y .- $.
  $d y A $. $d y B $. $d y C $. $d y D $. $d y E $. $d y F $.
  $d x y $.
  cgranorm.p $e |- P = ( Base ` G ) $.
  cgranorm.i $e |- I = ( Itv ` G ) $.
  cgranorm.k $e |- K = ( hlG ` G ) $.
  cgranorm.m $e |- .- = ( dist ` G ) $.
  cgranorm.g $e |- ( ph -> G e. TarskiG ) $.
  cgranorm.a $e |- ( ph -> A e. P ) $.
  cgranorm.b $e |- ( ph -> B e. P ) $.
  cgranorm.c $e |- ( ph -> C e. P ) $.
  cgranorm.d $e |- ( ph -> D e. P ) $.
  cgranorm.e $e |- ( ph -> E e. P ) $.
  cgranorm.f $e |- ( ph -> F e. P ) $.
  cgranorm.1 $e |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> ) $.
  $( Ray normalization: an angle congruence yields two points on the target
     rays carrying a full triangle congruence, together with the two arm
     lengths.  This is the forward direction of ~ iscgra (Schwabhauser 11.3)
     repackaged -- nothing is constructed; the distances are read off the
     `cgrG` with ~ cgr3simp1 and ~ cgr3simp2 .  No non-degeneracy hypothesis is
     needed or wanted: `cgrA` carries vertex distinctness intrinsically
     ( ~ cgrane1 through ~ cgrane4 ), and an extra hypothesis would obstruct the
     degenerate branches. $)
  cgranorm $p |- ( ph -> E. x e. P E. y e. P ( ( <" A B C "> ( cgrG ` G ) <" x E y "> /\ x ( K ` E ) D /\ y ( K ` E ) F ) /\ ( ( E .- x ) = ( B .- A ) /\ ( E .- y ) = ( B .- C ) ) ) )
      $= ( cs3 cv ccgrg cfv wbr w3a wrex co wceq wa wcel simpr cstrkg simpll
        simpld syl simprd eqid simplr simp1d cgr3simp1 tgcgrcomlr eqcomd
        cgr3simp2 jca ex reximdva imp ccgra iscgra mpbid reximddv3 )
         ADEFUGZBUHZICUHZUGZKUIUJZUKZVTGIMUJZUKZWAJWEUKZULZCHUMZWHIVTNUNZEDNUN
         ZUOZIWANUNZEFNUNZUOZUPZUPZCHUMZBHAVTHUQZUPZWIWRWTWHWQCHWTWAHUQZUPZWHW
         QXBWHUPZWHWPXBWHURZXCWLWOXCWKWJXCDEVTIHKLNORPXCAKUSUQZXCAWSWTXAWHUTZV
         AZSVBZXCADHUQZXGTVBZXCAEHUQZXGUAVBZXCAWSXFVCZXCAIHUQZXGUDVBZXCDEFVTHW
         CIWAKLNORPWCVDZXHXJXLXCAFHUQZXGUBVBZXMXOWTXAWHVEZXCWDWFWGXDVFZVGVHVIX
         CWNWMXCDEFVTHWCIWAKLNORPXPXHXJXLXRXMXOXSXTVJVIVKVKVLVMVNAVSGIJUGKVOUJ
         UKWIBHUMUFABCDEFGHIJKLMOPQSTUAUBUCUDUEVPVQVR $.
$}

${
  $d y ph $. $d y P $. $d y I $. $d y K $. $d y G $. $d y .- $.
  $d y A $. $d y B $. $d y C $. $d y J $.
  $d y X $. $d y E $. $d y Z $.
  cgrgptxfr.p $e |- P = ( Base ` G ) $.
  cgrgptxfr.i $e |- I = ( Itv ` G ) $.
  cgrgptxfr.m $e |- .- = ( dist ` G ) $.
  cgrgptxfr.g $e |- ( ph -> G e. TarskiG ) $.
  cgrgptxfr.a $e |- ( ph -> A e. P ) $.
  cgrgptxfr.b $e |- ( ph -> B e. P ) $.
  cgrgptxfr.c $e |- ( ph -> C e. P ) $.
  cgrgptxfr.x $e |- ( ph -> X e. P ) $.
  cgrgptxfr.e $e |- ( ph -> E e. P ) $.
  cgrgptxfr.z $e |- ( ph -> Z e. P ) $.
  cgrgptxfr.j $e |- ( ph -> J e. P ) $.
  cgrgptxfr.1 $e |- ( ph -> <" A B C "> ( cgrG ` G ) <" X E Z "> ) $.
  cgrgptxfr.2 $e |- ( ph -> J e. ( A I C ) ) $.
  $( Transfer a segment point across a triangle congruence: given
     `<" A B C "> cgrG <" X E Z ">` and `J` between `A` and `C`, the
     corresponding point on `( X I Z )` exists, with its betweenness, its two
     distances and the sub-triangle congruence.  GeoCoq reaches this through
     `l4_6` and `cong2_conga_cong`; here ~ cgrg3col4 (Schwabhauser 11.28)
     constructs the point with every pairwise distance and ~ tgbtwnxfr -- which
     *is* `l4_6` -- supplies the image betweenness.  The `A = C` case takes
     ~ cgrg3col4 's right disjunct, since ~ tgellng needs `A =/= C` and `cgrA`
     does not supply it. $)
  cgrgptxfr $p |- ( ph -> E. y e. P ( ( y e. ( X I Z ) /\ <" A B J "> ( cgrG ` G ) <" X E y "> ) /\ ( ( A .- J ) = ( X .- y ) /\ ( J .- C ) = ( y .- Z ) ) ) )
      $= ( cs4 cv ccgrg cfv wbr co wcel cs3 wa wceq eqid cstrkg simpll syl
        simplr w3a simpr tgcgr4 mpbid simprd simp1d simp3d tgcgrcomlr
        cgr3simp3 trgcgr tgbtwnxfr cgr3simp1 simp2d jca clng wo olcd wne w3o
        simpl 3mix1d tgellng mpbird orcd pm2.61dane cgrg3col4 reximddv3 )
         ACDEJUGZLGMBUHZUGZHUIUJZUKZWJLMIULZUMZCDJUNZLGWJUNZWLUKZUOZCJKULZLWJK
         ULZUPZJEKULZWJMKULZUPZUOZUOBFAWJFUMZUOZWMUOZWSXFXIWOWRXICJELFWLWJMHIK
         NPOWLUQZXIAHURUMZAXGWMUSZQUTZXIACFUMZXLRUTZXIAJFUMZXLUDUTZXIAEFUMZXLT
         UTZXIALFUMZXLUAUTZAXGWMVAZXIAMFUMZXLUCUTZXICJELFWLWJMHKNPXJXMXOXQXSYA
         YBYDXIXBDJKULZGWJKULZUPZEJKULZMWJKULZUPZXICDEUNZLGMUNZWLUKZXBYGYJVBZX
         IWMYMYNUOZXHWMVCZXICDEJFWLHIKLGMWJNPOXJXMXOXIADFUMZXLSUTZXSXQYAXIAGFU
         MZXLUBUTZYDYBVDZVEZVFZVGZXIEJMWJFHIKNPOXMXSXQYDYBXIXBYGYJUUCVHZVIZXIC
         DELFWLGMHIKNPOXJXMXOYRXSYAYTYDXIAYMXLUEUTZVJVKXIAJCEIULZUMZXLUFUTVLXI
         CDJLFWLGWJHKNPXJXMXOYRXQYAYTYBXICDELFWLGMHIKNPOXJXMXOYRXSYAYTYDUUGVMX
         IXBYGYJUUCVNXICJLWJFHIKNPOXMXOXQYAYBUUDVIVKVOXIXBXEUUDUUFVOVOABCDELFG
         MHHVPUJZJNQRSTUAUBUCUUJUQZUDUEAJCEUUJULZUMZCEUPZVQCEAUUNUOUUNUUMAUUNV
         CVRACEVSZUOZUUMUUNUUPUUMUUICJEIULZUMZECJIULZUMZVTUUPUUIUURUUTUUPAUUIA
         UUOWAZUFUTWBUUPFHIUUJCEJNUUKOUUPAXKUVAQUTUUPAXNUVARUTUUPAXRUVATUTAUUO
         VCUUPAXPUVAUDUTWCWDWEWFWGWH $.
$}

${
  hlorbtwn.p $e |- P = ( Base ` G ) $.
  hlorbtwn.i $e |- I = ( Itv ` G ) $.
  hlorbtwn.k $e |- K = ( hlG ` G ) $.
  hlorbtwn.l $e |- L = ( LineG ` G ) $.
  hlorbtwn.g $e |- ( ph -> G e. TarskiG ) $.
  hlorbtwn.d $e |- ( ph -> D e. P ) $.
  hlorbtwn.e $e |- ( ph -> E e. P ) $.
  hlorbtwn.w $e |- ( ph -> W e. P ) $.
  hlorbtwn.1 $e |- ( ph -> W e. ( D L E ) ) $.
  hlorbtwn.2 $e |- ( ph -> D =/= E ) $.
  hlorbtwn.3 $e |- ( ph -> W =/= E ) $.
  $( Three collinear points, the outer two distinct from the middle one, are
     arranged in exactly one of two ways: `D` and `W` on one half-line from `E`,
     or `E` between them.  ~ tgcolg gives the betweenness trichotomy and its
     first two disjuncts collapse into the half-line exit through ~ btwnhl2 .
     Generic ray/betweenness bookkeeping; ~ inagcgratrg uses it to route the
     collinear half of its case analysis. $)
  hlorbtwn $p |- ( ph -> ( D ( K ` E ) W \/ E e. ( D I W ) ) )
      $= ( co wcel cfv wbr wo wa cstrkg simpl syl simpr wne btwnhl2 hlcomd
        orcd olcd w3o tgellng mpbid mpjao3dan ) AIBDFUAZUBZBIDGUCZUDZDBIFUAZUB
         ZUEBIDFUAZUBZVEAVAUFZVCVEVHIBDCEFGUGJKLVHAICUBZAVAUHZQUIZVHABCUBZVJOU
         IZVHADCUBZVJPUIZVHAEUGUBZVJNUIZVHBDIBCEFGJKLVMVOVKVQVMAVAUJVHABDUKZVJ
         SUIVHAIDUKZVJTUIULUMUNAVGUFZVCVEVTIDBICEFGJKLVTAVIAVGUHZQUIZVTAVNWAPU
         IVTAVLWAOUIVTAVPWANUIWBAVGUJVTAVSWATUIVTAVRWASUIULUNAVEUFVEVCAVEUJUOA
         IBDHUAUBVAVGVEUPRACEFHBDIJMKNOPSQUQURUS $.
$}

${
  inagcgratrgmain.p $e |- P = ( Base ` G ) $.
  inagcgratrgmain.i $e |- I = ( Itv ` G ) $.
  inagcgratrgmain.k $e |- K = ( hlG ` G ) $.
  inagcgratrgmain.m $e |- .- = ( dist ` G ) $.
  inagcgratrgmain.g $e |- ( ph -> G e. TarskiG ) $.
  inagcgratrgmain.d $e |- ( ph -> D e. P ) $.
  inagcgratrgmain.e $e |- ( ph -> E e. P ) $.
  inagcgratrgmain.w $e |- ( ph -> W e. P ) $.
  inagcgratrgmain.x $e |- ( ph -> X e. P ) $.
  inagcgratrgmain.y $e |- ( ph -> Y e. P ) $.
  inagcgratrgmain.z $e |- ( ph -> Z e. P ) $.
  inagcgratrgmain.j $e |- ( ph -> J e. P ) $.
  inagcgratrgmain.s $e |- ( ph -> S e. P ) $.
  inagcgratrgmain.t $e |- ( ph -> T e. P ) $.
  inagcgratrgmain.q $e |- ( ph -> Q e. P ) $.
  inagcgratrgmain.de $e |- ( ph -> D =/= E ) $.
  inagcgratrgmain.jw $e |- ( ph -> J ( K ` E ) W ) $.
  inagcgratrgmain.sx $e |- ( ph -> S ( K ` Y ) X ) $.
  inagcgratrgmain.tz $e |- ( ph -> T ( K ` Y ) Z ) $.
  inagcgratrgmain.q1 $e |- ( ph -> Q e. ( S I T ) ) $.
  inagcgratrgmain.sub $e |- ( ph -> <" D E J "> ( cgrG ` G ) <" S Y Q "> ) $.
  $( In-angle transport, the non-degenerate main case, with its three
     constructions carried as hypotheses: `J` the segment point from ~ isinag ,
     `S` and `T` the normalized target arms from ~ cgranorm , and `Q` the
     transferred point from ~ cgrgptxfr .  Concludes the body of
     ~ inagcgratrg 's existential at the witness `Q`.
     **No ~ acopy and no half-plane fact**: the witness is the transferred point,
     not a fresh angle copy, which is what removes the non-collinearity
     obligations the route was once thought to carry. $)
  inagcgratrgmain $p |- ( ph -> ( Q ( inA ` G ) <" X Y Z "> /\ <" D E W "> ( cgrA ` G ) <" X Y Q "> ) )
      $= ( cs3 cinag cfv wbr ccgra cstrkg hlne1 ccgrg eqid cgr3simp2 necomd
        tgcgrneq wceq hlid olcd isinagd hlcomd inaghl cgrcgra cgrahl1 cgracom
        cgrahl2 jca ) ADNOPURHUSUTVABGMURNODURHVBUTVAAEOFNCPHIKDDQRSUKUIUFUJUA
         AEOFCHIKVCDDQRSUKUIUFUJUAUKAENOCHIKVCQRSUIUEUFUAUNVDAFPOCHIKVCQRSUJUG
         UFUAUOVDAODAGJODCHILQTRUAUCUHUFUKABGJECHVEUTZODHILQTRWAVFZUAUBUCUHUIU
         FUKUQVGZAJGAJMGCHIKVCQRSUHUDUCUAUMVDZVHZVIZVHZUPADDOKUTVADOVJADDOCHIK
         QRSUKUKUFUAWGVKZVLVMUEUGUKAENOCHIKVCQRSUIUEUFUAUNVNZAFPOCHIKVCQRSUJUG
         UFUAUOVNWHVOANODBCGMHIKQRUASUEUFUKUBUCUDANODBCGJHIKMQRSUAUEUFUKUBUCUH
         ABGJNCODHIKQRUASUBUCUHUEUFUKABGJECODHIKNQRSUAUBUCUHUIUFUKABGJECODHIKQ
         RUASUBUCUHUIUFUKULWEUQVPUEWIVQVRUDAJMGCHIKVCQRSUHUDUCUAUMVNVSVRVT $.
$}

${
  $( `v` is bound in the conclusion, so these are mandatory and propagate to
     every caller. $)
  $d v ph $.  $d v P $.   $d v I $.  $d v K $.  $d v G $.
  $d v D $.   $d v E $.   $d v W $.
  $d v X $.   $d v Y $.   $d v Z $.
  $d v J $.   $d v S $.   $d v T $.  $d v Q $.

  inagcgratrgw.p $e |- P = ( Base ` G ) $.
  inagcgratrgw.i $e |- I = ( Itv ` G ) $.
  inagcgratrgw.k $e |- K = ( hlG ` G ) $.
  inagcgratrgw.g $e |- ( ph -> G e. TarskiG ) $.
  inagcgratrgw.d $e |- ( ph -> D e. P ) $.
  inagcgratrgw.e $e |- ( ph -> E e. P ) $.
  inagcgratrgw.w $e |- ( ph -> W e. P ) $.
  inagcgratrgw.x $e |- ( ph -> X e. P ) $.
  inagcgratrgw.y $e |- ( ph -> Y e. P ) $.
  inagcgratrgw.z $e |- ( ph -> Z e. P ) $.
  inagcgratrgw.j $e |- ( ph -> J e. P ) $.
  inagcgratrgw.s $e |- ( ph -> S e. P ) $.
  inagcgratrgw.t $e |- ( ph -> T e. P ) $.
  inagcgratrgw.q $e |- ( ph -> Q e. P ) $.
  inagcgratrgw.de $e |- ( ph -> D =/= E ) $.
  inagcgratrgw.jw $e |- ( ph -> J ( K ` E ) W ) $.
  inagcgratrgw.sx $e |- ( ph -> S ( K ` Y ) X ) $.
  inagcgratrgw.tz $e |- ( ph -> T ( K ` Y ) Z ) $.
  inagcgratrgw.q1 $e |- ( ph -> Q e. ( S I T ) ) $.
  inagcgratrgw.sub $e |- ( ph -> <" D E J "> ( cgrG ` G ) <" S Y Q "> ) $.

  $( ~ inagcgratrgmain with the existential introduced at its own witness `Q`.
     Split out so that the substitution instance is built once, at the top
     level, rather than under the existential eliminations that produce `S`,
     `T` and `Q`. $)
  inagcgratrgw $p
    |- ( ph -> E. v e. P
         ( v ( inA ` G ) <" X Y Z ">
           /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( cv cs3 cinag cfv wbr ccgra wa wceq simpr breq1d eqidd s3eqd breq2d
        anbi12d cds eqid inagcgratrgmain rspcedvd ) ABUQZNOPURZIUSUTZVAZCHMURZ
         NOVOURZIVBUTZVAZVCEVPVQVAZVSNOEURZWAVAZVCBEDUJAVOEVDZVCZVRWCWBWEWGVOE
         VPVQAWFVEZVFWGVTWDVSWAWGNOVOENOWGNVGWGOVGWHVHVIVJACDEFGHIJKLIVKUTZMNO
         PQRSWIVLTUAUBUCUDUEUFUGUHUIUJUKULUMUNUOUPVMVN $.
$}

${
  $d v ph $.  $d v P $.   $d v I $.  $d v K $.  $d v G $.
  $d v D $.   $d v E $.   $d v F $.  $d v W $.
  $d v X $.   $d v Y $.   $d v Z $.
  $d v J $.   $d v S $.   $d v T $.
  $d y ph $.  $d y P $.   $d y I $.  $d y K $.  $d y G $.
  $d y D $.   $d y E $.   $d y F $.  $d y W $.
  $d y X $.   $d y Y $.   $d y Z $.
  $d y J $.   $d y S $.   $d y T $.  $d y v $.

  inagcgratrgxfr.p $e |- P = ( Base ` G ) $.
  inagcgratrgxfr.i $e |- I = ( Itv ` G ) $.
  inagcgratrgxfr.k $e |- K = ( hlG ` G ) $.
  inagcgratrgxfr.g $e |- ( ph -> G e. TarskiG ) $.
  inagcgratrgxfr.d $e |- ( ph -> D e. P ) $.
  inagcgratrgxfr.e $e |- ( ph -> E e. P ) $.
  inagcgratrgxfr.f $e |- ( ph -> F e. P ) $.
  inagcgratrgxfr.w $e |- ( ph -> W e. P ) $.
  inagcgratrgxfr.x $e |- ( ph -> X e. P ) $.
  inagcgratrgxfr.y $e |- ( ph -> Y e. P ) $.
  inagcgratrgxfr.z $e |- ( ph -> Z e. P ) $.
  inagcgratrgxfr.j $e |- ( ph -> J e. P ) $.
  inagcgratrgxfr.s $e |- ( ph -> S e. P ) $.
  inagcgratrgxfr.t $e |- ( ph -> T e. P ) $.
  inagcgratrgxfr.de $e |- ( ph -> D =/= E ) $.
  inagcgratrgxfr.1 $e |- ( ph -> J e. ( D I F ) ) $.
  inagcgratrgxfr.jw $e |- ( ph -> J ( K ` E ) W ) $.
  inagcgratrgxfr.sx $e |- ( ph -> S ( K ` Y ) X ) $.
  inagcgratrgxfr.tz $e |- ( ph -> T ( K ` Y ) Z ) $.
  inagcgratrgxfr.2 $e |- ( ph -> <" D E F "> ( cgrG ` G ) <" S Y T "> ) $.

  $( In-angle transport with the target arms already normalized to `S` and `T`:
     ~ cgrgptxfr transfers the segment point `J` to a point of `( S I T )`, and
     that one existential is eliminated here. $)
  inagcgratrgxfr $p
    |- ( ph -> E. v e. P
         ( v ( inA ` G ) <" X Y Z ">
           /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( vy cv co wcel cs3 ccgrg cfv wbr wa cds wceq cinag ccgra wrex eqid
        cgrgptxfr cstrkg simpl syl simpr simpld wne simprd inagcgratrgw
        rexlimddv ) AUQURZEFJUSZUTZCGKVAZEOWBVAZIVBVCZVDZVEZCKIVFVCZUSZEWBWJUS
         ZVGZKHWJUSZWBFWJUSZVGZVEZVEZBURZNOPVAIVHVCVDCGMVANOWSVAIVIVCVDVEBDVJU
         QDAUQCGHDOIJKWJEFQRWJVKTUAUBUCUIUFUJUHUPULVLAWBDUTZWRVEZVEZBCDWBEFGIJ
         KLMNOPQRSXBAIVMUTAXAVNZTVOXBACDUTXCUAVOXBAGDUTXCUBVOXBAMDUTXCUDVOXBAN
         DUTXCUEVOXBAODUTXCUFVOXBAPDUTXCUGVOXBAKDUTXCUHVOXBAEDUTXCUIVOXBAFDUTX
         CUJVOXBWTWRAXAVPZVQXBACGVRXCUKVOXBAKMGLVCVDXCUMVOXBAENOLVCZVDXCUNVOXB
         AFPXEVDXCUOVOXBWDWHXBWIWQXBWTWRXDVSZVQZVQXBWDWHXGVSVTWA $.
$}

${
  $d v ph $.  $d v P $.   $d v I $.  $d v K $.  $d v G $.
  $d v D $.   $d v E $.   $d v F $.  $d v W $.
  $d v X $.   $d v Y $.   $d v Z $.  $d v J $.
  $d x ph $.  $d x P $.   $d x I $.  $d x K $.  $d x G $.
  $d x D $.   $d x E $.   $d x F $.  $d x W $.
  $d x X $.   $d x Y $.   $d x Z $.  $d x J $.  $d x v $.
  $d y ph $.  $d y P $.   $d y I $.  $d y K $.  $d y G $.
  $d y D $.   $d y E $.   $d y F $.  $d y W $.
  $d y X $.   $d y Y $.   $d y Z $.  $d y J $.  $d y v $.
  $d x y $.

  inagcgratrgncol.p $e |- P = ( Base ` G ) $.
  inagcgratrgncol.i $e |- I = ( Itv ` G ) $.
  inagcgratrgncol.k $e |- K = ( hlG ` G ) $.
  inagcgratrgncol.g $e |- ( ph -> G e. TarskiG ) $.
  inagcgratrgncol.d $e |- ( ph -> D e. P ) $.
  inagcgratrgncol.e $e |- ( ph -> E e. P ) $.
  inagcgratrgncol.f $e |- ( ph -> F e. P ) $.
  inagcgratrgncol.w $e |- ( ph -> W e. P ) $.
  inagcgratrgncol.x $e |- ( ph -> X e. P ) $.
  inagcgratrgncol.y $e |- ( ph -> Y e. P ) $.
  inagcgratrgncol.z $e |- ( ph -> Z e. P ) $.
  inagcgratrgncol.j $e |- ( ph -> J e. P ) $.
  inagcgratrgncol.de $e |- ( ph -> D =/= E ) $.
  inagcgratrgncol.1 $e |- ( ph -> J e. ( D I F ) ) $.
  inagcgratrgncol.jw $e |- ( ph -> J ( K ` E ) W ) $.
  inagcgratrgncol.cgb $e
    |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.

  $( In-angle transport once the segment point `J` of ~ isinag is on the ray
     `EW`: ~ cgranorm normalizes the target arms and its two existentials are
     eliminated here, leaving ~ inagcgratrgxfr to do the transfer. $)
  inagcgratrgncol $p
    |- ( ph -> E. v e. P
         ( v ( inA ` G ) <" X Y Z ">
           /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( cs3 vx cv vy ccgrg cfv wbr w3a wrex cinag ccgra wa cds co wceq eqid
        cgranorm simpl reximi syl wcel cstrkg simpll simplr simpld simprd wne
        simpr simp2d simp3d simp1d inagcgratrgxfr ex rexlimdvva mpd )
         ACEFUKZULUMZMUNUMZUKZGUOUPZUQZWGLMJUPZUQZWHNWLUQZURZUNDUSZULDUSZBUMZL
         MNUKZGUTUPZUQZCEKUKZLMWRUKZGVAUPZUQZVBZBDUSZAWOMWGGVCUPZVDZECXHVDZVEZ
         MWHXHVDZEFXHVDZVEZVBZVBZUNDUSZULDUSWQAULUNCEFLDMNGHJXHOPQXHVFRSTUAUCU
         DUEUJVGXQWPULDXPWOUNDWOXOVHVIVIVJAWOXGULUNDDAWGDVKZWHDVKZVBZVBZWOXGYA
         WOVBZBCDWGWHEFGHIJKLMNOPQYBAGVLVKAXTWOVMZRVJYBACDVKYCSVJYBAEDVKYCTVJY
         BAFDVKYCUAVJYBAKDVKYCUBVJYBALDVKYCUCVJYBAMDVKYCUDVJYBANDVKYCUEVJYBAID
         VKYCUFVJYBXRXSAXTWOVNZVOYBXRXSYDVPYBACEVQYCUGVJYBAICFHVDVKYCUHVJYBAIK
         EJUPUQYCUIVJYBWKWMWNYAWOVRZVSYBWKWMWNYEVTYBWKWMWNYEWAWBWCWDWE $.
$}

${
  $d v ph $.  $d v P $.   $d v I $.  $d v K $.  $d v L $.  $d v G $.
  $d v D $.   $d v E $.   $d v F $.  $d v W $.
  $d v X $.   $d v Y $.   $d v Z $.
  $d x ph $.  $d x P $.   $d x I $.  $d x K $.  $d x L $.  $d x G $.
  $d x D $.   $d x E $.   $d x F $.  $d x W $.
  $d x X $.   $d x Y $.   $d x Z $.  $d x v $.

  inagcgratrgn.p $e |- P = ( Base ` G ) $.
  inagcgratrgn.i $e |- I = ( Itv ` G ) $.
  inagcgratrgn.k $e |- K = ( hlG ` G ) $.
  inagcgratrgn.l $e |- L = ( LineG ` G ) $.
  inagcgratrgn.g $e |- ( ph -> G e. TarskiG ) $.
  inagcgratrgn.d $e |- ( ph -> D e. P ) $.
  inagcgratrgn.e $e |- ( ph -> E e. P ) $.
  inagcgratrgn.f $e |- ( ph -> F e. P ) $.
  inagcgratrgn.w $e |- ( ph -> W e. P ) $.
  inagcgratrgn.x $e |- ( ph -> X e. P ) $.
  inagcgratrgn.y $e |- ( ph -> Y e. P ) $.
  inagcgratrgn.z $e |- ( ph -> Z e. P ) $.
  inagcgratrgn.in $e |- ( ph -> W ( inA ` G ) <" D E F "> ) $.
  inagcgratrgn.cgb $e
    |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.
  inagcgratrgn.1 $e |- ( ph -> -. ( W e. ( D L E ) \/ D = E ) ) $.

  $( In-angle transport, non-collinear case: unfold ~ isinag , eliminate its
     segment-point existential, and dispatch on the disjunct it carries --
     `x = E` to ~ inagcgrabtwn , `x ( K ` E ) W` to ~ inagcgratrgncol . $)
  inagcgratrgn $p
    |- ( ph -> E. v e. P
         ( v ( inA ` G ) <" X Y Z ">
           /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( vx cv co wcel wceq cfv wbr wo wa cs3 cinag ccgra wrex wne w3a
        cstrkg isinag mpbid simprd simpl syl adantr simpr simpld eleq1d wn
        inagcgrabtwn inagne1 inagcgratrgncol mpjaodan rexlimddv ) AUJUKZCFHULZ
         UMZWAEUNZWAKEIUOZUPZUQZURZBUKZLMNUSZGUTUOZUPZCEKUSZLMWIUSZGVAUOZUPZUR
         ZBDVBZUJDACEVCZFEVCZKEVCZVDZWHUJDVBZAKCEFUSZWKUPXBXCURUGAUJCEFDGHIVEK
         OPQUCTUAUBSVFVGVHAWADUMZWHURZURZWDWRWFXGWDURZBCDEFGHIJKLMNOPQRXGGVEUM
         ZWDXGAXIAXFVIZSVJZVKXGCDUMZWDXGAXLXJTVJZVKXGEDUMZWDXGAXNXJUAVJZVKXGFD
         UMZWDXGAXPXJUBVJZVKXGKDUMZWDXGAXRXJUCVJZVKXGLDUMZWDXGAXTXJUDVJZVKXGMD
         UMZWDXGAYBXJUEVJZVKXGNDUMZWDXGAYDXJUFVJZVKXGXDWJWOUPZWDXGAYFXJUHVJZVK
         XHWCEWBUMXGWCWDXGWCWGXGXEWHAXFVLZVHZVMZVKXHWAEWBXGWDVLVNVGXGKCEJULZUM
         ZCEUNZUQZVOZWDXGAYOXJUIVJVKVPXGWFURBCDEFGHWAIKLMNOPQXGXIWFXKVKXGXLWFX
         MVKXGXNWFXOVKXGXPWFXQVKXGXRWFXSVKXGXTWFYAVKXGYBWFYCVKXGYDWFYEVKXGXEWF
         XGXEWHYHVMVKXGWSWFXGAWSXJACEFDGHIKOPQUCTUAUBSUGVQVJVKXGWCWFYJVKXGWFVL
         XGYFWFYGVKVRXGWCWGYIVHVSVT $.
$}

$( Angle order (`leA`) and its witnesses: passing between "inside the angle"
   and `leA`, transporting a witness across a congruent target angle, and
   replacing either compared angle by a congruent one. $)


${
  inanglele.p $e |- P = ( Base ` G ) $.
  inanglele.i $e |- I = ( Itv ` G ) $.
  inanglele.k $e |- K = ( hlG ` G ) $.
  inanglele.g $e |- ( ph -> G e. TarskiG ) $.
  inanglele.a $e |- ( ph -> A e. P ) $.
  inanglele.b $e |- ( ph -> B e. P ) $.
  inanglele.c $e |- ( ph -> C e. P ) $.
  inanglele.y $e |- ( ph -> Y e. P ) $.
  inanglele.1 $e |- ( ph -> C ( inA ` G ) <" A B Y "> ) $.

  $( If `C` lies inside angle `<" A B Y ">`, then angle `<" A B C ">`
     is less than or equal to `<" A B Y ">`. $)
  inanglele $p
    |- ( ph -> <" A B C "> ( leA ` G ) <" A B Y "> )
      $= ( cleag cfv eqid inagne1 inagne3 necomd cgraid isleagd ) ABCDBECIFFST
         ZDJMNOPNOQUGUAPRABCDEFGHJKMLNOPABCIEFGHDJKLPNOQMRUBADCABCIEFGHDJKLPNO
         QMRUCUDUEUF $.
$}

${
  $( `v` is bound in the conclusion, so these are *mandatory* $d conditions and
     they propagate to every caller.  Without them the statement cannot be
     proved through `acopy`, whose own frame demands its witness be distinct
     from everything in scope; `hlcgrex` is the set.mm statement of the same
     shape and carries the same list.  `.-` and `L` are deliberately absent:
     neither occurs in this statement, so the proof supplies them internally
     with `eqid` rather than making all five callers pass them. $)
  $d ph v $.  $d P v $.   $d I v $.  $d K v $.  $d G v $.
  $d D v $.   $d E v $.   $d F v $.  $d W v $.
  $d X v $.   $d Y v $.   $d Z v $.

  inagcgratrg.p $e |- P = ( Base ` G ) $.
  inagcgratrg.i $e |- I = ( Itv ` G ) $.
  inagcgratrg.k $e |- K = ( hlG ` G ) $.
  inagcgratrg.g $e |- ( ph -> G e. TarskiG ) $.
  inagcgratrg.d $e |- ( ph -> D e. P ) $.
  inagcgratrg.e $e |- ( ph -> E e. P ) $.
  inagcgratrg.f $e |- ( ph -> F e. P ) $.
  inagcgratrg.x $e |- ( ph -> X e. P ) $.
  inagcgratrg.y $e |- ( ph -> Y e. P ) $.
  inagcgratrg.z $e |- ( ph -> Z e. P ) $.
  inagcgratrg.w $e |- ( ph -> W e. P ) $.
  inagcgratrg.in $e |- ( ph -> W ( inA ` G ) <" D E F "> ) $.
  inagcgratrg.cgb $e
    |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.

  $( Target-side in-angle transport: if `W` lies inside angle `<" D E F ">`
     and that angle is congruent to `<" X Y Z ">`, then some point inside
     `<" X Y Z ">` makes `<" X Y v ">` congruent to the sub-angle
     `<" D E W ">`.  The geometric core of ~ leawittrg . $)
  inagcgratrg $p
    |- ( ph -> E. v e. P
         ( v ( inA ` G ) <" X Y Z ">
           /\ <" D E W "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( clng cfv co wcel wceq wo cv cs3 cinag wbr ccgra wa wrex wn cstrkg
        adantr simpr inagcgrasubhl inagcgrasubbtwn eqid wi inagne1 neneqd
        orel2 syl mpd wne inagne3 hlorbtwn mpjaodan inagcgratrgn exmid a1i )
         AJCEGUGUHZUIZUJZCEUKZULZBUMZKLMUNZGUOUHZUPZCEJUNZKLWEUNZGUQUHZUPZURZB
         DUSZWDUTZAWDURZCJEIUHZUPZWNECJHUIZUJZWPWRURBCDEFGHIJKLMNOPWPGVAUJZWRA
         XAWDQVBZVBWPCDUJZWRAXCWDRVBZVBWPEDUJZWRAXEWDSVBZVBWPFDUJZWRAXGWDTVBZV
         BWPJDUJZWRAXIWDUDVBZVBWPKDUJZWRAXKWDUAVBZVBWPLDUJZWRAXMWDUBVBZVBWPMDU
         JZWRAXOWDUCVBZVBWPCEFUNZWFWKUPZWRAXRWDUFVBZVBWPWRVCVDWPWTURBCDEFGHIJK
         LMNOPWPXAWTXBVBWPXCWTXDVBWPXEWTXFVBWPXGWTXHVBWPXIWTXJVBWPXKWTXLVBWPXM
         WTXNVBWPXOWTXPVBWPJXQWGUPZWTAXTWDUEVBVBWPXRWTXSVBWPWTVCVEWPCDEGHIVTJN
         OPVTVFZXBXDXFXJWPWDWBAWDVCWPWCUTZWDWBVGAYBWDACEACEFDGHIJNOPUDRSTQUEVH
         ZVIVBWCWBVJVKVLACEVMWDYCVBAJEVMWDACEFDGHIJNOPUDRSTQUEVNVBVOVPAWOURBCD
         EFGHIVTJKLMNOPYAAXAWOQVBAXCWORVBAXEWOSVBAXGWOTVBAXIWOUDVBAXKWOUAVBAXM
         WOUBVBAXOWOUCVBAXTWOUEVBAXRWOUFVBAWOVCVQWDWOULAWDVRVSVP $.
$}

${
  $( Mirrors `inagcgratrg`'s mandatory $d list: `v` is bound in the conclusion
     here too, and this proof instantiates `inagcgratrg`'s witness with it. $)
  $d ph v $.  $d P v $.   $d I v $.  $d K v $.  $d G v $.
  $d D v $.   $d E v $.   $d F v $.  $d W v $.
  $d X v $.   $d Y v $.   $d Z v $.
  $d H v $.   $d U v $.   $d J v $.

  leawittrg.p $e |- P = ( Base ` G ) $.
  leawittrg.i $e |- I = ( Itv ` G ) $.
  leawittrg.k $e |- K = ( hlG ` G ) $.
  leawittrg.g $e |- ( ph -> G e. TarskiG ) $.
  leawittrg.d $e |- ( ph -> D e. P ) $.
  leawittrg.e $e |- ( ph -> E e. P ) $.
  leawittrg.f $e |- ( ph -> F e. P ) $.
  leawittrg.x $e |- ( ph -> X e. P ) $.
  leawittrg.y $e |- ( ph -> Y e. P ) $.
  leawittrg.z $e |- ( ph -> Z e. P ) $.
  leawittrg.h $e |- ( ph -> H e. P ) $.
  leawittrg.u $e |- ( ph -> U e. P ) $.
  leawittrg.j $e |- ( ph -> J e. P ) $.
  leawittrg.w $e |- ( ph -> W e. P ) $.
  leawittrg.in $e |- ( ph -> W ( inA ` G ) <" D E F "> ) $.
  leawittrg.cga $e
    |- ( ph -> <" H U J "> ( cgrA ` G ) <" D E W "> ) $.
  leawittrg.cgb $e
    |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.

  $( Target-side `leA` witness transport: move a witness inside `<" D E F ">`
     across a congruent target angle `<" X Y Z ">`, carrying the angle
     `<" H U J ">` copied at that witness with it. $)
  leawittrg $p
    |- ( ph -> E. v e. P
         ( v ( inA ` G ) <" X Y Z ">
           /\ <" H U J "> ( cgrA ` G ) <" X Y v "> ) )
      $= ( cv cs3 cinag cfv wbr ccgra wa wcel simpr simpld cstrkg adantr simpl
        simprd cgratr jca inagcgratrg reximddv3 ) ABUNZNOPUOZHUPUQZURZCFMUOZNO
         VLUOZHUSUQZURZUTZVOIEKUOZVQVRURZUTBDAVLDVAZUTZVTUTZVOWBWEVOVSWDVTVBZV
         CWEIEKCDOFMHNJVLLQRWDHVDVAZVTAWGWCTVEVESWDIDVAZVTAWHWCUGVEVEWDEDVAZVT
         AWIWCUHVEVEWDKDVAZVTAWJWCUIVEVEWDCDVAZVTAWKWCUAVEVEWDFDVAZVTAWLWCUBVE
         VEWDMDVAZVTAWMWCUJVEVEWDWAVPVRURZVTAWNWCULVEVEWDNDVAZVTAWOWCUDVEVEWDO
         DVAZVTAWPWCUEVEVEWEAWCWDVTVFVGWEVOVSWFVGVHVIABCDFGHJLMNOPQRSTUAUBUCUD
         UEUFUJUKUMVJVK $.
$}


${
  $d ph w $.  $d A w $.   $d B w $.  $d C w $.
  $d D w $.   $d E w $.   $d F w $.  $d G w $.
  $d P w $.   $d X w $.   $d Y w $.  $d Z w $.
  $d ph v $.  $d A v $.   $d B v $.  $d C v $.
  $d D v $.   $d E v $.   $d F v $.  $d G v $.
  $d P v $.   $d X v $.   $d Y v $.  $d Z v $.
  $d v w $.
  $( `I` and `K` joined the list when `leawittrg`'s witness became a mandatory
     variable with $d against them; both are dummies here. $)
  $d I v $.   $d K v $.   $d I w $.  $d K w $.

  leacgrtrg.p $e |- P = ( Base ` G ) $.
  leacgrtrg.i $e |- I = ( Itv ` G ) $.
  leacgrtrg.k $e |- K = ( hlG ` G ) $.
  leacgrtrg.g $e |- ( ph -> G e. TarskiG ) $.
  leacgrtrg.a $e |- ( ph -> A e. P ) $.
  leacgrtrg.b $e |- ( ph -> B e. P ) $.
  leacgrtrg.c $e |- ( ph -> C e. P ) $.
  leacgrtrg.x $e |- ( ph -> X e. P ) $.
  leacgrtrg.y $e |- ( ph -> Y e. P ) $.
  leacgrtrg.z $e |- ( ph -> Z e. P ) $.
  leacgrtrg.d $e |- ( ph -> D e. P ) $.
  leacgrtrg.e $e |- ( ph -> E e. P ) $.
  leacgrtrg.f $e |- ( ph -> F e. P ) $.
  leacgrtrg.1 $e |- ( ph -> <" A B C "> ( leA ` G ) <" X Y Z "> ) $.
  leacgrtrg.2 $e |- ( ph -> <" X Y Z "> ( cgrA ` G ) <" D E F "> ) $.

  $( Target-side `leA` transport: replacing the larger angle by a congruent
     angle preserves the angle order.  Proved from ~ leawittrg and ~ isleag ,
     the witness form of `leA`. $)
  leacgrtrg $p
    |- ( ph -> <" A B C "> ( leA ` G ) <" D E F "> )
      $= ( cs3 cleag cfv wbr vv cv cinag ccgra wa wrex vw wcel cstrkg adantr
        simpl simprd simpr simpld leawittrg isleag mpbid r19.29a mpbird )
         ABCDUJZEGHUJZIUKULZUMUNUOZVNIUPULZUMZVMEGVPUJZIUQULZUMZURZUNFUSZAUTUO
         ZLMNUJZVQUMZVMLMWDUJZVTUMZURZWCUTFAWDFVAZURZWIURZUNLFCMNIBJDKWDEGHOPQ
         WKIVBVAZWIAWMWJRVCVCWKLFVAZWIAWNWJUBVCVCWKMFVAZWIAWOWJUCVCVCWKNFVAZWI
         AWPWJUDVCVCWKEFVAZWIAWQWJUEVCVCWKGFVAZWIAWRWJUFVCVCWKHFVAZWIAWSWJUGVC
         VCWKBFVAZWIAWTWJSVCVCWKCFVAZWIAXAWJTVCVCWKDFVAZWIAXBWJUAVCVCWLAWJWKWI
         VDVEWLWFWHWKWIVFZVGWLWFWHXCVEWKWEVNVTUMZWIAXDWJUIVCVCVHAVMWEVOUMWIUTF
         USUHAUTBCDLFMNIORSTUAUBUCUDVIVJVKAUNBCDEFGHIORSTUAUEUFUGVIVL $.
$}

${
  leacgrsrc.p $e |- P = ( Base ` G ) $.
  leacgrsrc.i $e |- I = ( Itv ` G ) $.
  leacgrsrc.k $e |- K = ( hlG ` G ) $.
  leacgrsrc.g $e |- ( ph -> G e. TarskiG ) $.
  leacgrsrc.a $e |- ( ph -> A e. P ) $.
  leacgrsrc.b $e |- ( ph -> B e. P ) $.
  leacgrsrc.c $e |- ( ph -> C e. P ) $.
  leacgrsrc.d $e |- ( ph -> D e. P ) $.
  leacgrsrc.e $e |- ( ph -> E e. P ) $.
  leacgrsrc.f $e |- ( ph -> F e. P ) $.
  leacgrsrc.h $e |- ( ph -> H e. P ) $.
  leacgrsrc.u $e |- ( ph -> U e. P ) $.
  leacgrsrc.j $e |- ( ph -> J e. P ) $.
  leacgrsrc.1 $e |- ( ph -> <" A B C "> ( leA ` G ) <" D E F "> ) $.
  leacgrsrc.2 $e |- ( ph -> <" A B C "> ( cgrA ` G ) <" H U J "> ) $.
  $d ph w $.  $d A w $.  $d B w $.  $d C w $.
  $d D w $.   $d E w $.  $d F w $.  $d G w $.
  $d H w $.   $d J w $.  $d P w $.  $d U w $.

  $( Source-side `leA` transport: replacing the smaller angle by a congruent
     angle preserves the angle order.  The counterpart of ~ leacgrtrg , proved
     directly from the witness form of `leA` ( ~ isleag , ~ isleagd ). $)
  leacgrsrc $p
    |- ( ph -> <" H U J "> ( leA ` G ) <" D E F "> )
      $= ( vw cv cs3 cinag cfv wbr ccgra wa cleag wcel cstrkg adantr eqid
        simpl simprd simpr simpld cgracom cgratr isleagd wrex isleag mpbid
        r19.29a ) AUJUKZEHIULZJUMUNZUOZBCDULZEHVNULZJUPUNZUOZUQZKGMULZVOJURUNZ
         UOUJFAVNFUSZUQZWBUQZKGMEFHIJWDVNOWFJUTUSZWBAWHWERVAZVAZWFKFUSZWBAWKWE
         UEVAZVAZWFGFUSZWBAWNWEUFVAZVAZWFMFUSZWBAWQWEUGVAZVAZWFEFUSZWBAWTWEUBV
         AZVAZWFHFUSZWBAXCWEUCVAZVAZWFIFUSZWBAXFWEUDVAVAWDVBWGAWEWFWBVCZVDZWGV
         QWAWFWBVEZVFWGKGMBFHCDJELVNNOPWJQWMWPWSWFBFUSZWBAXJWESVAZVAZWFCFUSZWB
         AXMWETVAZVAZWFDFUSZWBAXPWEUAVAZVAZWGBCDKFGMJLNOPWJQXLXOXRWMWPWSWFVRWC
         VTUOZWBAXSWEUIVAVAVGXBXEXHWGVQWAXIVDVHVIAVRVOWDUOWBUJFVJUHAUJBCDEFHIJ
         ORSTUAUBUCUDVKVLVM $.
$}

$( Angle order under congruence of both compared angles ( ~ leacgrtr ), used by
   ~ tgextalt2 . $)


${
  leacgrtr.p $e |- P = ( Base ` G ) $.
  leacgrtr.i $e |- I = ( Itv ` G ) $.
  leacgrtr.k $e |- K = ( hlG ` G ) $.
  leacgrtr.s $e |- .<_ = ( leA ` G ) $.
  leacgrtr.g $e |- ( ph -> G e. TarskiG ) $.
  leacgrtr.a $e |- ( ph -> A e. P ) $.
  leacgrtr.b $e |- ( ph -> B e. P ) $.
  leacgrtr.c $e |- ( ph -> C e. P ) $.
  leacgrtr.d $e |- ( ph -> D e. P ) $.
  leacgrtr.e $e |- ( ph -> E e. P ) $.
  leacgrtr.f $e |- ( ph -> F e. P ) $.
  leacgrtr.h $e |- ( ph -> H e. P ) $.
  leacgrtr.u $e |- ( ph -> U e. P ) $.
  leacgrtr.j $e |- ( ph -> J e. P ) $.
  leacgrtr.x $e |- ( ph -> X e. P ) $.
  leacgrtr.y $e |- ( ph -> Y e. P ) $.
  leacgrtr.z $e |- ( ph -> Z e. P ) $.
  leacgrtr.1 $e |- ( ph -> <" A B C "> .<_ <" D E F "> ) $.
  leacgrtr.2 $e |- ( ph -> <" A B C "> ( cgrA ` G ) <" H U J "> ) $.
  leacgrtr.3 $e |- ( ph -> <" D E F "> ( cgrA ` G ) <" X Y Z "> ) $.

  $( GeoCoq `l11_30` analogue: `leA` is preserved when both compared angles
     are replaced by congruent angles. $)
  leacgrtr $p
    |- ( ph -> <" H U J "> .<_ <" X Y Z "> )
      $= ( cs3 cleag cfv wbr breqi sylib leacgrsrc leacgrtrg sylibr )
         AKGMUSZPQRUSZJUTVAZVBVHVIOVBAKGMPFQRJLNEHISTUAUCUJUKULUGUHUIUMUNUOABC
         DEFGHIJKLMNSTUAUCUDUEUFUGUHUIUJUKULABCDUSZEHIUSZOVBVKVLVJVBUPVKVLOVJU
         BVCVDUQVEURVFVHVIOVJUBVCVG $.
$}

$( The exterior-angle theorem ~ tgexta2 and its route.  Throughout, the
   triangle is `A B C` with the side `B C` extended beyond `C` to `D`, so the
   exterior angle is `<" A C D ">` and the remote interior angles are those at
   `A` and `B`.

   The construction is the classical one: reflect `B` through the midpoint of
   `A` and `C`.  The reflected point carries the interior angle at `A` onto an
   angle at `C` ( ~ tgmircgra ) and lies inside the exterior angle
   ( ~ tgexta2lem1_inag ), which gives the non-strict bound ~ tgextale ; the
   strictness comes from the open half-plane facts ending in ~ tgextancgra . $)

${
  tgmircgrg.p $e |- P = ( Base ` G ) $.
  tgmircgrg.m $e |- .- = ( dist ` G ) $.
  tgmircgrg.i $e |- I = ( Itv ` G ) $.
  tgmircgrg.l $e |- L = ( LineG ` G ) $.
  tgmircgrg.g $e |- ( ph -> G e. TarskiG ) $.
  tgmircgrg.a $e |- ( ph -> A e. P ) $.
  tgmircgrg.b $e |- ( ph -> B e. P ) $.
  tgmircgrg.c $e |- ( ph -> C e. P ) $.
  tgmircgrg.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  $( Reflecting `B` through the midpoint of `A` and `C` carries triangle
     `C A B` onto `A C P`, where `P` is the reflected point.  The dimension
     condition the `mid*` family carries is discharged from the
     non-collinearity through ~ tgatgdim2 , not taken as a hypothesis. $)
  tgmircgrg $p |- ( ph -> <" C A B "> ( cgrG ` G ) <" A C ( ( ( pInvG ` G ) ` ( A ( midG ` G ) C ) ) ` B ) "> )
      $= ( ccgrg cfv cmid co cmir eqid tgatgdim2 midcl mircl eqidd tgcgrcoml
        wceq ismidb mpbird oveq1d miriso eqtrd eqcomd fveq2d mirmir oveq2d
        eqtr3d trgcgr ) ADBCBEFSTZDCBDFUATZUBZFUCTZTZTZFIJKVBUDNQOPOQAVDEVEFGH
         VFICJKLMVEUDZNABDEFGIJKLNACDBEFGHJMLNPQORUEZOQUFZVFUDZPUGABDBDEFGIJKL
         NOQOQABDIUBUHUIADVGIUBZBCIUBZAVLBVFTZVGIUBVMADVNVGIADVNUJZVDVDUJZAVDU
         HZABDEVEFGVDIJKLNVIOQVHVJUKZULZUMAVDEVEFGHVFIBCJKLMVHNVJVKOPUNUOUPAVG
         DVFTZIUBCDIUBVGBIUBAVDEVEFGHVFICDJKLMVHNVJVKPQUNAVTBVGIAVTVNVFTBADVNV
         FVSUQAVDBEVEFGHVFIJKLMVHNVJVKOURUOUSUTVA $.
$}

${
  tgmircgra.p $e |- P = ( Base ` G ) $.
  tgmircgra.m $e |- .- = ( dist ` G ) $.
  tgmircgra.i $e |- I = ( Itv ` G ) $.
  tgmircgra.l $e |- L = ( LineG ` G ) $.
  tgmircgra.g $e |- ( ph -> G e. TarskiG ) $.
  tgmircgra.a $e |- ( ph -> A e. P ) $.
  tgmircgra.b $e |- ( ph -> B e. P ) $.
  tgmircgra.c $e |- ( ph -> C e. P ) $.
  tgmircgra.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  $( The angle congruence the exterior-angle theorem opens with: the interior
     angle at `A` in triangle `C A B` is congruent to the angle at `C` in the
     midpoint-reflected triangle.  This is ~ cgrcgra over ~ tgmircgrg ; the
     vertex distinctnesses come from the non-collinearity via ~ tgbcne and
     ~ tgacne . $)
  tgmircgra $p |- ( ph -> <" C A B "> ( cgrA ` G ) <" A C ( ( ( pInvG ` G ) ` ( A ( midG ` G ) C ) ) ` B ) "> )
      $= ( cmid cfv co cmir chlg eqid tgatgdim2 midcl mircl tgbcne tgacne
        necomd tgmircgrg cgrcgra ) ADBCBEDCBDFSTZUAZFUBTZTZTFGFUCTZJLNUQUDQOPO
         QAUNEUOFGHUPICJKLMUOUDNABDEFGIJKLNACDBEFGHJMLNPQORUEOQUFUPUDPUGACDBEF
         GHJLMNPQORUHACBACDBEFGHJLMNPQORUIUJABCDEFGHIJKLMNOPQRUKUL $.
$}

${
  $d ph q $.
  $d P q $.
  $d I q $.
  $d L q $.
  $d K q $.
  $d .- q $.
  $d G q $.
  $d A q $.
  $d B q $.
  $d C q $.
  $d D q $.
  tgexta2lem1_inag.p $e |- P = ( Base ` G ) $.
  tgexta2lem1_inag.m $e |- .- = ( dist ` G ) $.
  tgexta2lem1_inag.i $e |- I = ( Itv ` G ) $.
  tgexta2lem1_inag.l $e |- L = ( LineG ` G ) $.
  tgexta2lem1_inag.k $e |- K = ( hlG ` G ) $.
  tgexta2lem1_inag.g $e |- ( ph -> G e. TarskiG ) $.
  tgexta2lem1_inag.a $e |- ( ph -> A e. P ) $.
  tgexta2lem1_inag.b $e |- ( ph -> B e. P ) $.
  tgexta2lem1_inag.c $e |- ( ph -> C e. P ) $.
  tgexta2lem1_inag.d $e |- ( ph -> D e. P ) $.
  tgexta2lem1_inag.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgexta2lem1_inag.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgexta2lem1_inag.ne $e |- ( ph -> C =/= D ) $.
  $( The point obtained by reflecting `B` through the midpoint of `A` and `C`
     lies inside the exterior angle `<" A C D ">`.  Proved by Pasch on the
     midpoint and the extension, turned into an in-angle statement with
     ~ isinagd and moved from ray `C M` to ray `C A` by ~ inaghl . $)
  tgexta2lem1_inag $p |- ( ph -> ( ( ( pInvG ` G ) ` ( A ( midG ` G ) C ) ) ` B ) ( inA ` G ) <" A C D "> )
      $= ( cmid cfv co cmir eqid ncolrot2 ncolcom ncolrot1 ncoltgdim2 midcl
        mircl vq cv wcel wa cs3 cinag wbr cvv adantr cstrkg elexd simpl simprd
        wne wceq wn wo ioran sylib eqidd midcgr eqcomd simpr tgcgreq eqtr3d ex
        necon3bd mpd necomd axtgcgrrflx eqtrd midbtwn mirbtwn tgbtwncom neqned
        btwnlng1 simpld jca nelne2 syl mirne oacgr mircgr ncolne1 tgsas2
        cgrane3 btwnhl1 orrd isinagd axtgpasch r19.29a btwnhl2 hlcomd hlid
        inaghl ) ABDGUEUFZUGZDEBFEGHICXLGUHUFZUFZUFZXOLNPAXLFXMGHJXNKCLMNOXMUI
         ZQABDFGHKLMNQAFGHJBDCLONQRTSAFGHJCBDLONQSRTAFGHJBCDLONQRSTAFGHJCDBLON
         QSTRUCUJZUKZULZUMZRTUNZXNUIZSUOZYATUAQAUPUQZXLEHUGZURZYDDXOHUGZURZUSZ
         XOXLDEUTGVAUFVBUPFAYDFURZUSZYIUSZXLDEFGHIVCXOYDLNPYKXOFURZYIAYMYJYCVD
         ZVDZYKXLFURZYIAYPYJYAVDVDYKDFURZYIAYQYJTVDZVDZYKEFURZYIAYTYJUAVDVDYLG
         VEYKGVEURZYIAUUAYJQVDZVDZVFYLAYJYKYIVGZVHZYKXLDVIZYIAUUFYJABDVJZVKZUU
         FACBDJUGZURZVKZUUHAUUJUUGVLZVKZUUKUUHUSZXSUUJUUGVMZVNZVHZAUUGXLDAXLDV
         JZUUGAUURUSZXLBDUUSXLDXLBFGHKLMNAUUAUURQVDZAYPUURYAVDZAYQUURTVDZUVAAB
         FURZUURRVDZAXLDKUGZXLBKUGZVJZUURAUVFUVEABDXLFGHKLMNQXTRTAXLVOZVPZVQZV
         DZAUURVRZVSZUVLVTZWAZWBZWCZVDVDYKEDVIZYIAUVRYJADEUDWDZVDVDYKXODVIZYIA
         UVTYJADXOACBXLXOFDXLGHILNPQSRYAYCTYAABXLCDFXLXOGHKLMNQRYASTYAYCABXLKU
         GZUVEDXLKUGZAUWAUVFUVEAFGHKBXLLMNQRYAWEZUVIWFZAUWBUVEAFGHKDXLLMNQTYAW
         EZVQZWFZABXLCDFBXOGHKLNMQRYASTRYCABDFGHKLMNQXTRTWGZAXOXLCFGHKLMNQYCYA
         SAXLCFXMGHJXNKLMNOXPQYAYBSWHZWIZAUUHXLBVIZUUQAUUGXLBAXLBVJZUUGAUWLUSZ
         XLBDAUWLVRZUWMXLBXLDFGHKLMNAUUAUWLQVDZAYPUWLYAVDZAUVCUWLRVDZUWPAYQUWL
         TVDZAUVFUVEVJZUWLUVIVDZUWNVSZVTZWAZWBZWCZAXLUUIURZUUKUSZXLCVIZAUXFUUK
         AFGHJBDXLLNOQRTYAABDUUQWJZUWHWKZAUUKUUHUUPWLZWMZXLCUUIWNZWOZUVQAXOXLA
         XLCFXMGHJXNKLMNOXPQYAYBSAXLCUXNWDZWPZWDZWQZAXLXOKUGZXLCKUGZAXLCFXMGHJ
         XNKLMNOXPQYAYBSWRZVQZAFGHJBCDLNOQRSTUCWSZWTZXAZWDZVDZVDZYLYFYHYKYIVRZ
         WLYLYDDVJZYDXODIUFZVBZYLUYJVKZUYLYLUYMUSZDXOYDYDFGHILNPYLYQUYMYSVDYLY
         MUYMYOVDYLYJUYMUUEVDZYLUUAUYMUUCVDUYOYLYHUYMYLYFYHUYIVHVDYLDXOVIUYMYL
         XODUYHWDVDUYNYDDYLUYMVRWJXBWAXCXDAFXLGHKDXOECUPLMNQYCUASYATUWIACDEFGH
         KLMNQSTUAUBWIXEXFRUAYCAXLBDFGHIVELNPYARTQABDXLEFGHILNPRTYAQUAUWHUXIUV
         QXGXHAEEDFGHILNPUAUATQUVSXIAXOXODFGHILNPYCYCTQUYFXIXJ $.
$}

${
  tgextale.p $e |- P = ( Base ` G ) $.
  tgextale.m $e |- .- = ( dist ` G ) $.
  tgextale.i $e |- I = ( Itv ` G ) $.
  tgextale.l $e |- L = ( LineG ` G ) $.
  tgextale.k $e |- K = ( hlG ` G ) $.
  tgextale.g $e |- ( ph -> G e. TarskiG ) $.
  tgextale.a $e |- ( ph -> A e. P ) $.
  tgextale.b $e |- ( ph -> B e. P ) $.
  tgextale.c $e |- ( ph -> C e. P ) $.
  tgextale.d $e |- ( ph -> D e. P ) $.
  tgextale.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextale.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgextale.ne $e |- ( ph -> C =/= D ) $.
  $( The non-strict exterior-angle bound, a checkpoint only.  `tgmircgra`
     gives the reflected copy of the interior angle, `tgexta2lem1_inag` puts
     that copy inside the exterior angle; `inanglele` turns "inside" into `leA`
     and `leacgrsrc` transports the bound along the congruence (flipped with
     `cgracom`).  No new geometry.  This bound is deliberately too weak for
     `tgaas`, whose contradiction branch already holds an angle congruence and
     so satisfies `leA` for free -- strictness comes later, and only `tgexta2`
     is the exterior-angle theorem. $)
  tgextale $p |- ( ph -> <" C A B "> ( leA ` G ) <" A C D "> )
      $= ( cmid cfv co cmir eqid tgatgdim2 midcl mircl tgexta2lem1_inag
        inanglele tgmircgra cgracom leacgrsrc ) ABDCBDGUEUFZUGZGUHUFZUFZUFZBFB
         DEGDHCILNPQRTAUSFUTGHJVAKCLMNOUTUIZQABDFGHKLMNQACDBFGHJLONQSTRUCUJZRT
         UKZVAUIZSULZRTUATRSABDVBFGHIELNPQRTVGUAABCDEFGHIJKLMNOPQRSTUAUBUCUDUM
         UNADBCBFDVBGHILNQPTRSRTVGABCDFGHJKLMNOQRSTUCUOUPUQ $.
$}

${
  tgextancd.p $e |- P = ( Base ` G ) $.
  tgextancd.m $e |- .- = ( dist ` G ) $.
  tgextancd.i $e |- I = ( Itv ` G ) $.
  tgextancd.l $e |- L = ( LineG ` G ) $.
  tgextancd.g $e |- ( ph -> G e. TarskiG ) $.
  tgextancd.a $e |- ( ph -> A e. P ) $.
  tgextancd.b $e |- ( ph -> B e. P ) $.
  tgextancd.c $e |- ( ph -> C e. P ) $.
  tgextancd.d $e |- ( ph -> D e. P ) $.
  tgextancd.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextancd.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgextancd.ne $e |- ( ph -> C =/= D ) $.
  $( The target-side non-collinearity of the exterior angle.  Line `CD`
     is line `CB` -- `C` lies between `B` and `D`, and `C =/= D` -- so `A` is
     off it exactly because the triangle is non-degenerate.  This is
     `acopyeu`'s `acopy.2` frame hypothesis in `tgextancgra`, and it is what
     excludes `isinag`'s `x = C` branch in `tgextahp`. $)
  tgextancd $p |- ( ph -> -. ( A e. ( C L D ) \/ C = D ) )
      $= ( co wcel wn wceq wa wo ncolcom ioran sylib simpld simprd neqned
        necomd tgbtwncom btwncolg2 olcnd tglineelsb2 eleq2d mtbid neneqd jca
        sylibr ) ABDEIUCZUDZUEZDEUFZUEZUGVFVHUHUEAVGVIABDCIUCZUDZVFAVKUEZDCUFZ
         UEZAVKVMUHZUEZVLVNUGZAFGHICDBKNMOQRPUAUIZVKVMUJZUKZULAVJVEBAFDCEGHIKM
         NORQADCAVLVNVTUMZUNSADEUBUOAEVJUDVMAFGHIDCEKNMORQSACDEFGHJKLMOQRSTUPU
         QWAURUSUTVAADEUBVBVCVFVHUJVD $.
$}

${
  tgextamirn.p $e |- P = ( Base ` G ) $.
  tgextamirn.m $e |- .- = ( dist ` G ) $.
  tgextamirn.i $e |- I = ( Itv ` G ) $.
  tgextamirn.l $e |- L = ( LineG ` G ) $.
  tgextamirn.g $e |- ( ph -> G e. TarskiG ) $.
  tgextamirn.a $e |- ( ph -> A e. P ) $.
  tgextamirn.b $e |- ( ph -> B e. P ) $.
  tgextamirn.c $e |- ( ph -> C e. P ) $.
  tgextamirn.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  $( The midpoint-reflected point is off line `AC`.  If it were on that
     line, `mirln` -- whose centre-on-the-line hypothesis is the midpoint,
     itself on `AC` -- would put its reflection there too, and `mirmir` says
     that reflection is `B`, contradicting the triangle's non-collinearity.
     This is the strengthening `inA` cannot give: it is what turns "inside the
     angle" into an open half-plane fact. $)
  tgextamirn $p |- ( ph -> -. ( ( ( pInvG ` G ) ` ( A ( midG ` G ) C ) ) ` B ) e. ( A L C ) )
      $= ( cmid cfv co cmir wcel wn wceq wo wa ncolrot1 ncolcom ioran sylib
        simpld eqid cstrkg adantr tgatgdim2 midcl mirmir crn ncolne2 tgelrnln
        midbtwn btwncolg1 neneqd olcnd simpr mirln eqeltrrd mtand ) ACBDFSTZUA
         ZFUBTZTZTZBDHUAZUCZCVOUCZAVQUDZBDUEZUDZAVQVSUFUDVRVTUGAEFGHDBCJMLNQOP
         AEFGHCDBJMLNPQORUHUIVQVSUJUKULAVPUGZVNVMTCVOWAVKCEVLFGHVMIJKLMVLUMZAF
         UNUCZVPNUOZAVKEUCVPABDEFGIJKLNACDBEFGHJMLNPQORUPZOQUQZUOVMUMZACEUCVPP
         UOURWAVKVNVOEVLFGHVMIJKLMWBWDWGAVOHUSUCVPAEFGHBDJLMNOQAEFGHBCDJLMNOPQ
         RUTZVAUOAVKVOUCZVPAWIVSAEFGHBDVKJMLNOQWFABDEFGIJKLNWEOQVBVCABDWHVDVEU
         OAVPVFVGVHVI $.
$}

${
  $d a b $. $d a t $. $d b t $.
  $d u v $. $d u w $. $d v w $.
  $d u a $. $d u b $. $d u t $. $d v a $. $d v b $. $d v t $. $d w a $. $d w b $. $d w t $.
  $d ph u $. $d ph v $. $d ph w $.
  $d P u $. $d P v $. $d P w $. $d I u $. $d I v $. $d I w $.
  $d L u $. $d L v $. $d L w $. $d K u $. $d K v $. $d K w $.
  $d G u $. $d G v $. $d G w $. $d A u $. $d A v $. $d A w $.
  $d C u $. $d C v $. $d C w $. $d D u $. $d D v $. $d D w $.
  $d W u $. $d W v $. $d W w $. $d X u $. $d X v $. $d X w $.
  $d ph a $. $d ph b $. $d ph t $.
  $d P a $. $d P b $. $d P t $.
  $d I a $. $d I b $. $d I t $.
  $d L a $. $d L b $. $d L t $.
  $d K a $. $d K b $. $d K t $.
  $d G a $. $d G b $. $d G t $.
  $d A a $. $d A b $. $d A t $.
  $d C a $. $d C b $. $d C t $.
  $d D a $. $d D b $. $d D t $.
  $d W a $. $d W b $. $d W t $.
  $d X a $. $d X b $. $d X t $.
  tgextahpl.p $e |- P = ( Base ` G ) $.
  tgextahpl.m $e |- .- = ( dist ` G ) $.
  tgextahpl.i $e |- I = ( Itv ` G ) $.
  tgextahpl.l $e |- L = ( LineG ` G ) $.
  tgextahpl.k $e |- K = ( hlG ` G ) $.
  tgextahpl.g $e |- ( ph -> G e. TarskiG ) $.
  tgextahpl.a $e |- ( ph -> A e. P ) $.
  tgextahpl.c $e |- ( ph -> C e. P ) $.
  tgextahpl.d $e |- ( ph -> D e. P ) $.
  tgextahpl.w $e |- ( ph -> W e. P ) $.
  tgextahpl.x $e |- ( ph -> X e. P ) $.
  tgextahpl.ncd $e |- ( ph -> -. ( A e. ( C L D ) \/ C = D ) ) $.
  tgextahpl.nw $e |- ( ph -> -. W e. ( A L C ) ) $.
  tgextahpl.xad $e |- ( ph -> X e. ( A I D ) ) $.
  tgextahpl.xk $e |- ( ph -> X ( K ` C ) W ) $.
  $( The generic open half-plane core.  From a point `X` between `A` and
     `D` that is on the half-line from `C` through `W`, with `W` off line `AC`,
     both `X` and `D` and both `X` and `W` land on the same side of line `AC`
     (two `colhp` applications), and `hpgcom` / `hpgtr` compose them.  `X =/= C`
     is read off `.xk` by `hlne1`, so no `x = C` case reaches here.  The `$d`s
     are on proof dummies only -- `colhp`'s class abstraction needs its own
     bound variables -- so nothing propagates to callers. $)
  tgextahpl $p |- ( ph -> W ( ( hpG ` G ) ` ( A L C ) ) D )
      $= ( vt co vu cv cdif wcel vv wa vw wrex copab va vb ncolne1 tgelrnln
        wceq simpl eleq1d simpr anbi12d simpll simplr oveq12d eleq12d
        cbvrexdva cbvopabv chpg cfv wbr wn adantr cstrkg hlcomd hlln wne
        tglinecom necomd hlne1 eleqtrd tglineelsb2 eqtrd eleqtrrd mtand jca
        tglinerflx2 wo btwncolg2 tgbtwncom btwncolg3 w3a ishlg mpbid simp3d
        mpjaodan colhp mpbird hpgcom ncolne2 tglinerflx1 nelne2 syl2anc
        btwnhl1 hpgtr ) AUHKLDBCIUIZEFGIUJUKZEXKULZUMZUNUKZXMUMZUOZUPUKZXLXOGU
         IZUMZUPXKUQZUOZUJUNURZUSUTMOPRAEFGIBCMOPRSTAEFGIBCDMOPRSTUAUDVAZVBZUB
         YBUSUKZXMUMZUTUKZXMUMZUOZUHUKZYFYHGUIZUMZUHXKUQZUOZUJUNUSUTXLYFVCZXOY
         HVCZUOZXQYJYAYNYRXNYGXPYIYRXLYFXMYPYQVDZVEZYRXOYHXMYPYQVFZVEZVGZYRXTY
         MUPUHXKYRXRYKVCZUOZXRYKXSYLYRUUDVFZUUEXLYFXOYHGYPYQUUDVHZYPYQUUDVIZVJ
         ZVKZVLZVGZVMZUCAUHLKXKEFGIYCUSUTMOPRYEUCUUMUBALKXKFVNVOZVOZVPLKCHVOZV
         PZLXKUMZVQZUOAUUQUUSUGAUURKXKUMZUEAUURUOZKLCIUIZXKUVAKLCEFGHIMOQAKEUM
         ZUURUBVRZALEUMZUURUCVRZACEUMZUURTVRZAFVSUMZUURRVRZPUVALKCEFGHVSMOQUVF
         UVDUVHUVJAUUQUURUGVRZVTZWAZUVAXKCBIUIZUVBUVAEBCFGIMOPUVJABEUMZUURSVRZ
         UVHABCWBZUURYDVRZWCZUVAUVNCLIUIZUVBUVAECBLFGIMOPUVJUVHUVPACBWBZUURABC
         YDWDZVRZUVFALCWBZUURALKCEFGHVSMOQUCUBTRUGWEZVRZUVALXKUVNAUURVFZUVSWFZ
         WGZUVAECLFGIMOPUVJUVHUVFACLWBZUURALCUWEWDZVRZWCZWHZWHZWIZWJZWKAUHLKCX
         KEFGHIYCUSUTMOPRYEUCUUMUBAEBCFGIMOPRSTYDWLALCKGUIZUMZCLKIUIUMLKVCWMKC
         LGUIZUMZAUWSUOEFGILKCMPOAUVIUWSRVRAUVEUWSUCVRAUVCUWSUBVRAUVGUWSTVRAUW
         SVFWNAUXAUOZEFGILKCMPOAUVIUXARVRZAUVEUXAUCVRZAUVCUXAUBVRZAUVGUXATVRZU
         XBCKLEFGJMNOUXCUXFUXEUXDAUXAVFWOWPAUWDKCWBZUWSUXAWMZAUUQUWDUXGUXHWQUG
         ALKCEFGHVSMOQUCUBTRWRWSWTXAQXBXCXDUAALDUUOVPLDBHVOZVPZUUSUOAUXJUUSABD
         LCEFGHMOQSUAUCRTUFAEFGIBCDMOPRSTUAUDXEABLABXKUMUUSBLWBAEBCFGIMOPRSTYD
         XFZUWQBLXKXGXHWDXIUWQWKAUHLDBXKEFGHIYCUSUTMOPRYEUCUUMUAUXKAEFGILDBMPO
         RUCUASUFWNQXBXCXJ $.
$}

${
  tgextamirnhl.p $e |- P = ( Base ` G ) $.
  tgextamirnhl.m $e |- .- = ( dist ` G ) $.
  tgextamirnhl.i $e |- I = ( Itv ` G ) $.
  tgextamirnhl.l $e |- L = ( LineG ` G ) $.
  tgextamirnhl.k $e |- K = ( hlG ` G ) $.
  tgextamirnhl.g $e |- ( ph -> G e. TarskiG ) $.
  tgextamirnhl.a $e |- ( ph -> A e. P ) $.
  tgextamirnhl.b $e |- ( ph -> B e. P ) $.
  tgextamirnhl.c $e |- ( ph -> C e. P ) $.
  tgextamirnhl.d $e |- ( ph -> D e. P ) $.
  tgextamirnhl.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextamirnhl.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgextamirnhl.ne $e |- ( ph -> C =/= D ) $.
  $( The midpoint-reflected point is not on the ray from
     `C` through `D`.  If it were, then -- ray `CD` being the extension of `BC`
     -- it would lie on line `CB`; `mirln2`, the converse of the `mirln` used
     in `tgextamirn`, would put the midpoint of `A` and `C` on that line too;
     and the midpoint is collinear with `A` and `C`, so `A` would land on line
     `CB`, contradicting the triangle's non-collinearity.  `M =/= C` comes from
     `ismidb` / `mirinv` / `mirne`, not from `midbtwn`. $)
  tgextamirnhl $p |- ( ph -> -. D ( K ` C ) ( ( ( pInvG ` G ) ` ( A ( midG ` G ) C ) ) ` B ) )
      $= ( cmid cfv co cmir wbr wcel wn wceq wo wa ncolcom ioran sylib simpld
        cstrkg adantr tgatgdim2 midcl midbtwn tgbtwncom btwncolg3 eqidd eqid
        ismidb mpbird wne ncolne2 necomd eqeq1d mirinv bitrd necon3bid mpbid
        mirne eqnetrd neneqd olcnd simprd neqned crn tgelrnln tglinerflx2
        mircl simpr hlcomd hlln tglinecom eleqtrd btwncolg2 tglineelsb2
        eleqtrrd mirln2 mtand ) AECBDGUEUFZUGZGUHUFZUFZUFZDIUFZUIZBDCJUGZUJZAX
         FUKZDCULZUKZAXFXHUMZUKZXGXIUNZAFGHJCDBLONQSTRUCUOZXFXHUPZUQZURAXDUNZB
         DWSJUGZXEXPBXQUJDWSULZXPFGHJDWSBLONAGUSUJZXDQUTZADFUJZXDTUTZAWSFUJZXD
         ABDFGHKLMNQACDBFGHJLONQSTRUCVAZRTVBZUTZABFUJXDRUTAWSDBHUGUJXDABWSDFGH
         KLMNQRYETABDFGHKLMNQYDRTVCVDUTVEAXRUKXDADWSADBXAUFZWSADYGULZWSWSULZAW
         SVFZABDFWTGHWSKLMNQYDRTWTVGZYEVHZVIZAWSBFWTGHJXAKLMNOYKQYEXAVGZRAWSBA
         DBVJZWSBVJZABDAFGHJBCDLNOQRSTUCVKZVLZADBWSBADBULZYGBULZWSBULZADYGBYMV
         MZAWSBFWTGHJXAKLMNOYKQYEYNRVNZVOZVPZVQZVLZVRZVSZVTUTWAXPFDCWSGHJLNOXT
         YBACFUJXDSUTADCVJXDADCAXGXIXOWBZWCZUTYFAWSDVJXDADWSUUIVLUTXPWSCXEFWTG
         HJXAKLMNOYKXTYNAXEJWDUJXDAFGHJDCLNOQTSUUKWEUTYFACXEUJXDAFDCGHJLNOQTSU
         UKWFUTXPXBDEJUGZXEXPXBEDJUGUULXPXBEDFGHIJLNPAXBFUJZXDAWSFWTGHJXAKCLMN
         OYKQYEYNSWGZUTZAEFUJZXDUAUTZYBXTOXPEXBDFGHIUSLNPUUQUUOYBXTAXDWHWIWJXP
         FEDGHJLNOXTUUQYBAEDVJXDADEUDVLZUTWKWLAXEUULULXDAFDCEGHJLNOQTSUUKUAUUR
         AEXEUJXHAFGHJDCELONQTSUAACDEFGHKLMNQSTUAUBVDWMUUJWAWNUTWOWPWNWOWQ $.
$}

${
  $d ph x $. $d P x $. $d .- x $. $d I x $. $d L x $.
  $d K x $. $d G x $.
  $d A x $. $d B x $. $d C x $. $d D x $.
  tgextahp.p $e |- P = ( Base ` G ) $.
  tgextahp.m $e |- .- = ( dist ` G ) $.
  tgextahp.i $e |- I = ( Itv ` G ) $.
  tgextahp.l $e |- L = ( LineG ` G ) $.
  tgextahp.k $e |- K = ( hlG ` G ) $.
  tgextahp.g $e |- ( ph -> G e. TarskiG ) $.
  tgextahp.a $e |- ( ph -> A e. P ) $.
  tgextahp.b $e |- ( ph -> B e. P ) $.
  tgextahp.c $e |- ( ph -> C e. P ) $.
  tgextahp.d $e |- ( ph -> D e. P ) $.
  tgextahp.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextahp.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgextahp.ne $e |- ( ph -> C =/= D ) $.
  $( The reflected point and `D` lie on the same OPEN half-plane
     of line `AC` -- the fact `acopyeu` requires and `inA` does not give.
     `tgexta2lem1_inag` puts the reflected point inside the exterior angle,
     which is non-strict: `isinag`'s witness clause is
     `( x = C \/ x ( K ` C ) P' )`, so a point inside an angle may sit on a
     boundary ray.  The `x = C` branch collapses to `( A e. ( C L D ) \/ C = D )`
     and is killed by `tgextancd`; the main branch is `tgextahpl`, whose
     off-line input is `tgextamirn`.  The `$d`s are the mandatory ones `isinag`
     carries for the witness variable. $)
  tgextahp $p |- ( ph -> ( ( ( pInvG ` G ) ` ( A ( midG ` G ) C ) ) ` B ) ( ( hpG ` G ) ` ( A L C ) ) D )
      $= ( vx cv co wcel wceq cmid cfv cmir wbr wo wa chpg wne w3a wrex cs3
        cinag tgexta2lem1_inag cstrkg eqid tgatgdim2 midcl mircl isinag mpbid
        simprd adantr simpr simprrl eqeltrrd btwncolg2 wn tgextancd pm2.21dd
        simprl tgextamirn tgextahpl simprrr mpjaodan rexlimddv ) AUEUFZBEHUGZU
         HZWEDUIZWECBDGUJUKZUGZGULUKZUKZUKZDIUKZUMZUNZUOZWMEBDJUGZGUPUKZUKZUMZ
         UEFABDUQZEDUQZWMDUQZURZWQUEFUSZAWMBDEUTGVAUKUMXEXFUOABCDEFGHIJKLMNOPQ
         RSTUAUBUCUDVBAUEBDEFGHIVCWMLNPAWJFWKGHJWLKCLMNOWKVDZQABDFGHKLMNQACDBF
         GHJLONQSTRUCVEZRTVFZWLVDZSVGZRTUAQVHVIVJAWEFUHZWQUOZUOZWHXAWOXNWHUOZB
         DEJUGZUHZDEUIZUNZXAXOFGHJDEBLONXNGVCUHZWHAXTXMQVKZVKXNDFUHZWHAYBXMTVK
         ZVKXNEFUHZWHAYDXMUAVKZVKXNBFUHZWHAYFXMRVKZVKXOWEDWFXNWHVLXNWGWHAXLWGW
         PVMZVKVNVOXNXSVPZWHAYIXMABCDEFGHJKLMNOQRSTUAUBUCUDVQZVKZVKVRXNWOUOBDE
         FGHIJKWMWELMNOPXNXTWOYAVKXNYFWOYGVKXNYBWOYCVKXNYDWOYEVKXNWMFUHZWOAYLX
         MXKVKVKXNXLWOAXLWQVSVKXNYIWOYKVKXNWMWRUHZVPZWOAYNXMABCDFGHJKLMNOQRSTU
         CVTVKVKXNWGWOYHVKXNWOVLWAAXLWGWPWBWCWD $.
$}

${
  $d a b $. $d a t $. $d b t $.
  $d u v $. $d u w $. $d v w $.
  $d u a $. $d u b $. $d u t $. $d v a $. $d v b $. $d v t $. $d w a $. $d w b $. $d w t $.
  $d ph u $. $d ph v $. $d ph w $.
  $d P u $. $d P v $. $d P w $. $d I u $. $d I v $. $d I w $.
  $d L u $. $d L v $. $d L w $. $d K u $. $d K v $. $d K w $.
  $d G u $. $d G v $. $d G w $. $d A u $. $d A v $. $d A w $.
  $d B u $. $d B v $. $d B w $. $d C u $. $d C v $. $d C w $.
  $d D u $. $d D v $. $d D w $. $d .- u $. $d .- v $. $d .- w $.
  $d ph a $. $d ph b $. $d ph t $.
  $d P a $. $d P b $. $d P t $.
  $d I a $. $d I b $. $d I t $.
  $d L a $. $d L b $. $d L t $.
  $d K a $. $d K b $. $d K t $.
  $d G a $. $d G b $. $d G t $.
  $d A a $. $d A b $. $d A t $.
  $d B a $. $d B b $. $d B t $.
  $d C a $. $d C b $. $d C t $.
  $d D a $. $d D b $. $d D t $.
  $d .- a $. $d .- b $. $d .- t $.
  tgextancgra.p $e |- P = ( Base ` G ) $.
  tgextancgra.m $e |- .- = ( dist ` G ) $.
  tgextancgra.i $e |- I = ( Itv ` G ) $.
  tgextancgra.l $e |- L = ( LineG ` G ) $.
  tgextancgra.k $e |- K = ( hlG ` G ) $.
  tgextancgra.g $e |- ( ph -> G e. TarskiG ) $.
  tgextancgra.a $e |- ( ph -> A e. P ) $.
  tgextancgra.b $e |- ( ph -> B e. P ) $.
  tgextancgra.c $e |- ( ph -> C e. P ) $.
  tgextancgra.d $e |- ( ph -> D e. P ) $.
  tgextancgra.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextancgra.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgextancgra.ne $e |- ( ph -> C =/= D ) $.
  $( The exterior angle is NOT congruent to the remote interior angle --
     the strictness `tgextale` cannot give, and what `tgaas`'s contradiction
     branch needs.  The exterior angle is `<" A C D ">`, at the extension of
     `B C` beyond `C`.  The tail of GeoCoq's `l11_41_aux`, run through `acopyeu`
     rather than `conga_cop__or_out_ts`: a congruent exterior angle would, by
     angle-construction uniqueness, put the midpoint-reflected point of
     `tgmircgra` on the ray `C D` -- the two rays make congruent angles with
     the shared base ray `C A` and, by `tgextahp` and `hpgid`, lie on the same
     open half-plane of line `AC` -- which `tgextamirnhl` forbids.  Both of
     `acopyeu`'s non-collinearity hypotheses are discharged, not assumed:
     source side by rotating the triangle's own `ncol`, target side by
     `tgextancd`. $)
  tgextancgra $p |- ( ph -> -. <" C A B "> ( cgrA ` G ) <" A C D "> )
      $= ( cs3 ccgra cfv wbr cmid co cmir tgextamirnhl wa cstrkg wcel adantr
        wceq wo wn ncolrot1 tgextancd eqid tgatgdim2 midcl mircl simpr
        tgmircgra chpg vt vu cv cdif vv vw wrex copab va vb ncolne2 tgelrnln
        simpl eleq1d anbi12d simpll simplr oveq12d eleq12d cbvrexdva cbvopabv
        ioran sylib simpld necomd tglinerflx2 wne tglinecom eleqtrd
        tglineelsb2 mtand hpgid tgextahp acopyeu ) ADBCUEZBDEUEZGUFUGZUHZECBDG
         UIUGZUJZGUKUGZUGZUGZDIUGUHABCDEFGHIJKLMNOPQRSTUAUBUCUDULAXFUMDBCBFDEG
         HIJKEXKLNMAGUNUOZXFQUPADFUOZXFTUPZABFUOZXFRUPZACFUOXFSUPXPXNAEFUOZXFU
         AUPZOADBCJUJUOBCUQURUSXFAFGHJDBCLONQTRSAFGHJCDBLONQSTRUCUTUTUPABDEJUJ
         ZUOZDEUQZURZUSZXFABCDEFGHJKLMNOQRSTUAUBUCUDVAZUPXRAXKFUOXFAXHFXIGHJXJ
         KCLMNOXIVBQABDFGHKLMNQACDBFGHJLONQSTRUCVCRTVDXJVBSVEUPPAXFVFAXCBDXKUE
         XEUHXFABCDFGHJKLMNOQRSTUCVGUPAEEBDJUJZGVHUGZUGZUHXFAVIEYEFGHJVJVKZFYE
         VLZUOZVMVKZYIUOZUMZVNVKZYHYKHUJZUOZVNYEVOZUMZVJVMVPVQVRLNOQAFGHJBDLNO
         QRTAFGHJBCDLNOQRSTUCVSZVTUAYRVQVKZYIUOZVRVKZYIUOZUMZVIVKZYTUUBHUJZUOZ
         VIYEVOZUMVJVMVQVRYHYTUQZYKUUBUQZUMZYMUUDYQUUHUUKYJUUAYLUUCUUKYHYTYIUU
         IUUJWAWBUUKYKUUBYIUUIUUJVFWBWCUUKYPUUGVNVIYEUUKYNUUEUQZUMZYNUUEYOUUFU
         UKUULVFUUMYHYTYKUUBHUUIUUJUULWDUUIUUJUULWEWFWGWHWCWIAEYEUOZXTAXTUSZYA
         USZAYCUUOUUPUMYDXTYAWJWKWLAUUNUMZBDBJUJZXSABUURUOUUNAFDBGHJLNOQTRABDY
         SWMZWNUPUUQFDBEGHJLNOAXLUUNQUPZAXMUUNTUPZAXOUUNRUPZADBWOUUNUUSUPAXQUU
         NUAUPAEDWOUUNADEUDWMUPUUQEYEUURAUUNVFUUQFBDGHJLNOUUTUVBUVAABDWOUUNYSU
         PWPWQWRWQWSWTUPAXKEYGUHXFABCDEFGHIJKLMNOPQRSTUAUBUCUDXAUPXBWS $.
$}

${
  tgextaoa.p $e |- P = ( Base ` G ) $.
  tgextaoa.m $e |- .- = ( dist ` G ) $.
  tgextaoa.i $e |- I = ( Itv ` G ) $.
  tgextaoa.k $e |- K = ( hlG ` G ) $.
  tgextaoa.g $e |- ( ph -> G e. TarskiG ) $.
  tgextaoa.a $e |- ( ph -> A e. P ) $.
  tgextaoa.b $e |- ( ph -> B e. P ) $.
  tgextaoa.c $e |- ( ph -> C e. P ) $.
  tgextaoa.d $e |- ( ph -> D e. P ) $.
  tgextaoa.e $e |- ( ph -> E e. P ) $.
  tgextaoa.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextaoa.ext2 $e |- ( ph -> C e. ( A I E ) ) $.
  tgextaoa.cb $e |- ( ph -> C =/= B ) $.
  tgextaoa.ca $e |- ( ph -> C =/= A ) $.
  tgextaoa.dc $e |- ( ph -> D =/= C ) $.
  tgextaoa.ce $e |- ( ph -> C =/= E ) $.
  $( The two exterior angles at `C` are VERTICAL, hence congruent.  Ray
     `C D` is opposite ray `C B` and ray `C E` is opposite ray `C A`, so
     `<" B C E ">` and `<" A C D ">` have both legs flipped.  One `sacgr`
     (Schwabhaeuser 11.13, GeoCoq `l11_13`) does it in a single shot, because
     `sacgr` flips the first slot of each side independently: the premise it
     wants is `<" D C E "> ( cgrA ` G ) <" E C D ">`, a bare angle reversal by
     `cgraswap`, needing no non-collinearity at all.  `oacgr` (11.14) would
     prove the same thing from two supplements and is not used. $)
  tgextaoa $p |- ( ph -> <" B C E "> ( cgrA ` G ) <" A C D "> )
      $= ( cgraswap tgbtwncom sacgr ) AEDGGFDEHIKCBLNMPTSUAUASTRQAEDGFHIJLNPOT
         SUAUFUGUHACDEFHIKLMNPRSTUBUIABDGFHIKLMNPQSUAUCUIUDUEUJ $.
$}

${
  tgextalt1.p $e |- P = ( Base ` G ) $.
  tgextalt1.m $e |- .- = ( dist ` G ) $.
  tgextalt1.i $e |- I = ( Itv ` G ) $.
  tgextalt1.l $e |- L = ( LineG ` G ) $.
  tgextalt1.k $e |- K = ( hlG ` G ) $.
  tgextalt1.s $e |- .<_ = ( leA ` G ) $.
  tgextalt1.g $e |- ( ph -> G e. TarskiG ) $.
  tgextalt1.a $e |- ( ph -> A e. P ) $.
  tgextalt1.b $e |- ( ph -> B e. P ) $.
  tgextalt1.c $e |- ( ph -> C e. P ) $.
  tgextalt1.d $e |- ( ph -> D e. P ) $.
  tgextalt1.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextalt1.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgextalt1.ne $e |- ( ph -> C =/= D ) $.
  $( ~ tgexta2 's FIRST conjunct, strict -- the remote interior angle at `A` is
     strictly less than the exterior angle at `C`.  ~ tgextale and
     ~ tgextancgra deliver both halves already, but stated about `<" C A B ">`;
     ~ tgexta2 wants `<" B A C ">`, the same angle read backwards.  So this is
     ~ cgraswap plus two transports: ~ leacgrsrc for the `leA` half, and
     ~ cgratr under ~ mtand for the negation -- if `<" B A C ">` were congruent
     to the exterior angle then so would `<" C A B ">` be, which
     ~ tgextancgra forbids. $)
  tgextalt1 $p
    |- ( ph -> ( <" B A C "> .<_ <" A C D ">
                 /\ -. <" B A C "> ( cgrA ` G ) <" A C D "> ) )
      $= ( cs3 wbr ccgra cfv wn cleag tgextale ncolne2 necomd ncolne1 cgraswap
        leacgrsrc breqi sylibr tgextancgra wa cstrkg wcel adantr simpr cgratr
        mtand jca ) ACBDUGZBDEUGZKUHZVJVKGUIUJZUHZUKAVJVKGULUJZUHVLADBCBFBDEGC
         HDIMOQSUBTUATUBUCUATUBABCDEFGHIJLMNOPQSTUAUBUCUDUEUFUMADBCFGHIMOSQUBT
         UAABDAFGHJBCDMOPSTUAUBUEUNZUOZAFGHJBCDMOPSTUAUBUEUPZUQZURVJVKKVORUSUT
         AVNDBCUGZVKVMUHABCDEFGHIJLMNOPQSTUAUBUCUDUEUFVAAVNVBDBCCFDBDGBHEIMOAG
         VCVDVNSVEQADFVDZVNUBVEZABFVDZVNTVEZACFVDZVNUAVEZWFWDWBAVTVJVMUHVNVSVE
         WDWBAEFVDVNUCVEAVNVFVGVHVI $.
$}

${
  tgextalt2.p $e |- P = ( Base ` G ) $.
  tgextalt2.m $e |- .- = ( dist ` G ) $.
  tgextalt2.i $e |- I = ( Itv ` G ) $.
  tgextalt2.l $e |- L = ( LineG ` G ) $.
  tgextalt2.k $e |- K = ( hlG ` G ) $.
  tgextalt2.s $e |- .<_ = ( leA ` G ) $.
  tgextalt2.g $e |- ( ph -> G e. TarskiG ) $.
  tgextalt2.a $e |- ( ph -> A e. P ) $.
  tgextalt2.b $e |- ( ph -> B e. P ) $.
  tgextalt2.c $e |- ( ph -> C e. P ) $.
  tgextalt2.d $e |- ( ph -> D e. P ) $.
  tgextalt2.e $e |- ( ph -> E e. P ) $.
  tgextalt2.ext $e |- ( ph -> C e. ( B I D ) ) $.
  tgextalt2.ext2 $e |- ( ph -> C e. ( A I E ) ) $.
  tgextalt2.ncol $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgextalt2.ne $e |- ( ph -> C =/= D ) $.
  tgextalt2.ne2 $e |- ( ph -> C =/= E ) $.
  $( ~ tgexta2 's SECOND conjunct, strict, at a supplied second extension
     point `E`.  This is NOT a permutation of the first conjunct: `E` is a new
     point, `C` between `A` and `E`, and ~ tgextale / ~ tgextancgra are applied
     a second time at the reconfigured triangle (the roles of `A` and `B`
     exchanged, exterior angle `<" B C E ">`).  ~ tgextaoa then identifies
     `<" B C E ">` with `<" A C D ">` as vertical angles, and the two halves
     are transported across that congruence -- ~ leacgrtr for `leA`, and
     ~ cgratr under ~ mtand for the negation, which ~ leacgrtr cannot move.
     `E` is existentially constructed by ~ tgexta2 , not here. $)
  tgextalt2 $p
    |- ( ph -> ( <" A B C "> .<_ <" A C D ">
                 /\ -. <" A B C "> ( cgrA ` G ) <" A C D "> ) )
      $= ( cs3 wbr ccgra cfv wn cleag ncolrot2 ncolcom ncolrot1 tgextale breqi
        sylibr ncolne1 necomd cgraswap ncolne2 tgextaoa leacgrtr tgextancgra
        wa cstrkg wcel adantr simpr cgratr cgracom mtand jca ) ABCDUKZBDEUKZLU
         LVSVTHUMUNZULZUOADCBCFCDGHBIDJLBDENPRSTUCUBUAUBUCUEUAUBUCUAUCUDADCBUK
         ZCDGUKZHUPUNZULWCWDLULACBDGFHIJKMNOPQRTUBUAUCUEUGAFHIKCBDNQPTUBUAUCAF
         HIKBCDNQPTUAUBUCAFHIKCDBNQPTUBUCUAUHUQZURZUSZUJUTWCWDLWESVAVBADCBFHIJ
         NPTRUCUBUAACDAFHIKCDBNPQTUBUCUAAFHIKCDBNQPTUBUCUAUHUSZVCZVDZABCAFHIKB
         CDNPQTUAUBUCUHVCZVDZVEZABCDEFGHIJMNOPRTUAUBUCUDUEUFUGWKABDAFHIKBCDNPQ
         TUAUBUCUHVFZVDZADEUIVDZUJVGZVHAWBWCWDWAULACBDGFHIJKMNOPQRTUBUAUCUEUGW
         HUJVIAWBVJZDCBBFDDEHCIGJNPAHVKVLZWBTVMZRADFVLZWBUCVMZACFVLZWBUBVMZABF
         VLZWBUAVMZXGXCAEFVLZWBUDVMZWSDCBBFDCDHBIEJNPXARXCXEXGXGXEXCAWCVSWAULW
         BWNVMXGXCXIAWBVNVOXEXCAGFVLWBUEVMAVTWDWAULWBACDGBFDEHIJNPTRUBUCUEUAUC
         UDWRVPVMVOVQVR $.
$}

${
  $( `y` is the second extension point, a proof-internal dummy: mandatory $d. $)
  $d ph y $.  $d P y $.   $d .- y $.  $d I y $.  $d L y $.
  $d K y $.   $d .<_ y $. $d G y $.
  $d A y $.   $d B y $.   $d C y $.   $d D y $.

  tgexta2.p $e |- P = ( Base ` G ) $.
  tgexta2.m $e |- .- = ( dist ` G ) $.
  tgexta2.i $e |- I = ( Itv ` G ) $.
  tgexta2.l $e |- L = ( LineG ` G ) $.
  tgexta2.k $e |- K = ( hlG ` G ) $.
  tgexta2.s $e |- .<_ = ( leA ` G ) $.
  tgexta2.g $e |- ( ph -> G e. TarskiG ) $.
  tgexta2.a $e |- ( ph -> A e. P ) $.
  tgexta2.b $e |- ( ph -> B e. P ) $.
  tgexta2.c $e |- ( ph -> C e. P ) $.
  tgexta2.d $e |- ( ph -> D e. P ) $.
  tgexta2.1 $e |- ( ph -> C e. ( B I D ) ) $.
  tgexta2.2 $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgexta2.3 $e |- ( ph -> C =/= D ) $.

  $( The exterior-angle theorem, GeoCoq `l11_41` -- BOTH remote interior
     angles of the triangle are STRICTLY less than the exterior angle at `C`.
     There is no `ltA` in `set.mm` and none is defined here, so strictness is
     carried inline as `leA` together with the non-congruence; the pair is what
     ~ tgaas 's contradiction branch needs, since a bare `leA` conclusion is
     satisfied by a congruence and so contradicts nothing ( ~ tgexta2n records
     that the pair is usable).  The second conjunct is not a permutation of the
     first: ~ axtgsegcon builds a second extension point `y` beyond `C` on line
     `A C`, ~ tgextalt2 reruns the construction there, and the two exterior
     angles are identified as vertical by ~ tgextaoa . $)
  tgexta2 $p
    |- ( ph ->
         ( ( <" B A C "> .<_ <" A C D ">
             /\ -. <" B A C "> ( cgrA ` G ) <" A C D "> )
           /\ ( <" A B C "> .<_ <" A C D ">
                /\ -. <" A B C "> ( cgrA ` G ) <" A C D "> ) ) )
      $= ( cs3 wbr ccgra cfv wn wa tgextalt1 vy cv co wcel wceq cstrkg adantr
        simpl simprd simpr simpld wo wne eqcomd ncolne2 necomd tgcgrneq
        tgextalt2 axtgsegcon r19.29a jca ) ACBDUGZBDEUGZKUHVOVPGUIUJZUHUKULBCD
         UGZVPKUHZVRVPVQUHZUKZULZABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUMADBUNUOZHUP
         ZUQZDWCLUPZDBLUPZURZULZWBUNFAWCFUQZULZWIULZBCDEFWCGHIJKLMNOPQRWKGUSUQ
         ZWIAWMWJSUTZUTZWKBFUQZWIAWPWJTUTZUTZWKCFUQZWIAWSWJUAUTUTWKDFUQZWIAWTW
         JUBUTZUTZWKEFUQZWIAXCWJUCUTUTWLAWJWKWIVAZVBZWKDCEHUPZUQZWIAXGWJUDUTUT
         WLWEWHWKWIVCZVDWKBCDJUPZUQZCDURZVEZUKZWIAXMWJUEUTUTWKDEVFZWIAXNWJUFUT
         UTWLDBDWCFGHLMNOWOXBWRXBXEWLWFWGWLWEWHXHVBVGWKDBVFZWIAXOWJABDAFGHJBCD
         MOPSTUAUBUEVHVIUTUTVJVKAUNDBFGHLBDMNOSTUBUBTVLVMVN $.
$}

${
  tgexta2n.p $e |- P = ( Base ` G ) $.
  tgexta2n.m $e |- .- = ( dist ` G ) $.
  tgexta2n.i $e |- I = ( Itv ` G ) $.
  tgexta2n.l $e |- L = ( LineG ` G ) $.
  tgexta2n.k $e |- K = ( hlG ` G ) $.
  tgexta2n.s $e |- .<_ = ( leA ` G ) $.
  tgexta2n.g $e |- ( ph -> G e. TarskiG ) $.
  tgexta2n.a $e |- ( ph -> A e. P ) $.
  tgexta2n.b $e |- ( ph -> B e. P ) $.
  tgexta2n.c $e |- ( ph -> C e. P ) $.
  tgexta2n.d $e |- ( ph -> D e. P ) $.
  tgexta2n.1 $e |- ( ph -> C e. ( B I D ) ) $.
  tgexta2n.2 $e |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) ) $.
  tgexta2n.3 $e |- ( ph -> C =/= D ) $.
  tgexta2n.cgr $e |- ( ph -> <" A B C "> ( cgrA ` G ) <" A C D "> ) $.
  $( `tgexta2`'s strictness is usable, not merely present -- a remote
     interior angle congruent to the exterior angle is contradictory, so
     anything follows.  This is the shape ~ tgaasexc consumes: that branch
     holds an angle congruence and must close on it, which the non-strict
     `leA`-only form of ~ tgexta2 could never let it do. $)
  tgexta2n $p |- ( ph -> ps )
      $= ( cs3 ccgra cfv wbr wn wa tgexta2 simprd pm2.21dd ) ACDEUIZCEFUIZHUJU
         KZULZBUHAURUSLULZVAUMZADCEUIZUSLULVDUSUTULUMUNVBVCUNACDEFGHIJKLMNOPQR
         STUAUBUCUDUEUFUGUOUPUPUQ $.
$}


$( The AAS assembly proper.  ~ tgaas1 reduces AAS to SAS by proving
   the side included between the two given angles congruent; everything from
   here to ~ tgaas1 exists to prove that one equality, by ruling out
   `( B .- C ) =/= ( E .- F )` with the exterior-angle theorem ~ tgexta2n .

   Nowhere in this cone is the third angle congruence `<" C A B "> ( cgrA ` G )
   <" F D E ">` derived from the two given ones: that inference is the angle-sum
   theorem and is false in absolute geometry. $)

${
  tgaasncol.p $e |- P = ( Base ` G ) $.
  tgaasncol.i $e |- I = ( Itv ` G ) $.
  tgaasncol.l $e |- L = ( LineG ` G ) $.
  tgaasncol.g $e |- ( ph -> G e. TarskiG ) $.
  tgaasncol.x $e |- ( ph -> X e. P ) $.
  tgaasncol.y $e |- ( ph -> Y e. P ) $.
  tgaasncol.z $e |- ( ph -> Z e. P ) $.
  tgaasncol.w $e |- ( ph -> W e. P ) $.
  tgaasncol.1 $e |- ( ph -> -. ( X e. ( Y L Z ) \/ Y = Z ) ) $.
  tgaasncol.2 $e |- ( ph -> ( W e. ( Z L Y ) \/ Z = Y ) ) $.
  tgaasncol.3 $e |- ( ph -> W =/= Z ) $.

  $( Slide a non-collinearity along the line it is off: if `X` is off line
     `Y Z` and `W` is a point of that line other than `Z`, then `X` is off line
     `Z W` too.  Lines `Z Y` and `Z W` coincide ( ~ tglineeltr ), which is what
     the exterior-angle hypothesis of ~ tgaasexc needs at the moving point. $)
  tgaasncol $p
    |- ( ph -> -. ( X e. ( Z L W ) \/ Z = W ) )
      $= ( co wcel wceq wo ncolcom wa cstrkg adantr wne ncolrot1 ncolne1
        necomd neneqd olcnd simpr tglineeltr orcd mtand ) AGIFEUAZUBZIFUCZUDZG
         IHEUAZUBZIHUCZUDABCDEHIGJLKMOPNRUEAVBUFZVDVEVFBIHGFCDEJKLACUGUBVBMUHA
         IBUBVBPUHAHBUBVBOUHAIHUIVBAHIABCDEHIGJKLMOPNABCDEHIGJLKMOPNRUJZUKZULZ
         UHAFBUBVBQUHAFIUIZVBTUHZAFVCUBZVBAVLVESAIHVIUMUNUHAGBUBVBNUHVFUTVAAVB
         UOVFIFVFFIVKULUMUNUPUQUR $.
$}

${
  tgaasexc.p $e |- P = ( Base ` G ) $.
  tgaasexc.m $e |- .- = ( dist ` G ) $.
  tgaasexc.i $e |- I = ( Itv ` G ) $.
  tgaasexc.l $e |- L = ( LineG ` G ) $.
  tgaasexc.g $e |- ( ph -> G e. TarskiG ) $.
  tgaasexc.d $e |- ( ph -> D e. P ) $.
  tgaasexc.e $e |- ( ph -> E e. P ) $.
  tgaasexc.s $e |- ( ph -> S e. P ) $.
  tgaasexc.t $e |- ( ph -> T e. P ) $.
  tgaasexc.1 $e |- ( ph -> -. ( D e. ( E L T ) \/ E = T ) ) $.
  tgaasexc.2 $e |- ( ph -> S e. ( E I T ) ) $.
  tgaasexc.3 $e |- ( ph -> S =/= E ) $.
  tgaasexc.4 $e |- ( ph -> S =/= T ) $.
  tgaasexc.5 $e
    |- ( ph -> <" D T E "> ( cgrA ` G ) <" D S E "> ) $.

  $( The contradiction branch of AAS, stated once for both orders of the two
     candidate points.  `S` lies strictly between `E` and `T`, and `D` is off
     the line, so `<" D S E ">` is an exterior angle of triangle `D T S` and is
     STRICTLY greater than the remote interior angle at `T` -- while the
     hypothesis says the two are congruent.  ~ tgexta2n turns that into
     anything. $)
  tgaasexc $p |- ( ph -> ps )
      $= ( chlg cfv cleag eqid tgbtwncom btwncolg1 tgaasncol ncolne2 ncolrot1
        ncolne1 necomd cgraid btwnhl1 cgrahl2 cgracom cgratr tgexta2n )
         ABCFEGDHIHUFUGZJHUHUGZKLMNOVCUIZVDUIPQTSRAGEFDHIKLMNPRSTUBUJZADHIJECG
         FLNOPQRTSUAADHIJFGELONPTRSVFUKUDULUCACFECDEFGHCIGVCLNPVEQTSQTRACFGCDF
         EHIVCLNPVEQTRQTSACFGCDFGHIVCELNVEPQTRQTRACFGDHIVCLNPVEQTRADHIJCGFLNOP
         QRTUAUMAGFADHIJGFCLNOPRTQADHIJGFCLONPRTQUAUNZUOZUPZUQSAFGECDHIVCLNVET
         RSPQVFVIUDURUSUTQSRUEVAVB $.
$}

${
  tgaasne.p $e |- P = ( Base ` G ) $.
  tgaasne.m $e |- .- = ( dist ` G ) $.
  tgaasne.i $e |- I = ( Itv ` G ) $.
  tgaasne.l $e |- L = ( LineG ` G ) $.
  tgaasne.k $e |- K = ( hlG ` G ) $.
  tgaasne.g $e |- ( ph -> G e. TarskiG ) $.
  tgaasne.d $e |- ( ph -> D e. P ) $.
  tgaasne.e $e |- ( ph -> E e. P ) $.
  tgaasne.f $e |- ( ph -> F e. P ) $.
  tgaasne.h $e |- ( ph -> H e. P ) $.
  tgaasne.1 $e |- ( ph -> -. ( D e. ( E L F ) \/ E = F ) ) $.
  tgaasne.2 $e |- ( ph -> H ( K ` E ) F ) $.
  tgaasne.3 $e |- ( ph -> F =/= H ) $.
  tgaasne.4 $e
    |- ( ph -> <" D F E "> ( cgrA ` G ) <" D H E "> ) $.

  $( Two DISTINCT points `F` and `H` on one half-line from `E`, subtending
     congruent angles at a point `D` off the line, are contradictory.  ~ ishlg
     unfolds the half-line to "one of them is strictly between `E` and the
     other" -- both sub-branches are proved, each by ~ tgaasexc on its own
     triangle, and they are not permutations of one another: the second needs
     the non-collinearity transported to line `E H` by ~ tgdefncol . $)
  tgaasne $p |- ( ph -> ps )
      $= ( co wcel wa cstrkg adantr wceq wo wn simpr wne cfv wbr w3a ishlg
        mpbid simp1d necomd cs3 ccgra tgaasexc cgraswaplr tgdefncol simp2d
        cgracom simp3d mpjaodan ) AHEFIUGZUHZBFEHIUGZUHZAVNUIBCDHFEGIKLMNOPAGU
         JUHZVNRUKACDUHZVNSUKAEDUHZVNTUKAHDUHZVNUBUKAFDUHZVNUAUKACEFKUGUHEFULU
         MUNVNUCUKAVNUOAHEUPZVNAWBFEUPZVNVPUMZAHFEJUQZURZWBWCWDUSZUDAHFEDGIJUJ
         MOQUBUATRUTZVAZVBUKAHFUPVNAFHUEVCUKACFEVDZCHEVDZGVEUQZURVNUFUKVFAVPUI
         BCDFHEGIKLMNOPAVQVPRUKAVRVPSUKAVSVPTUKAWAVPUAUKAVTVPUBUKACEHKUGUHEHUL
         UMUNVPAEFCEDHCGIKLMNOPRTUASTUBSUCACFECDHEGILMONRSUATSUBTUFVGVHUKAVPUO
         AWCVPAWBWCWDWIVIUKAFHUPVPUEUKAWKWJWLURVPACFECDHEGIJMORQSUATSUBTUFVJUK
         VFAWBWCWDWIVKVL $.
$}

${
  tgaascgra.p $e |- P = ( Base ` G ) $.
  tgaascgra.m $e |- .- = ( dist ` G ) $.
  tgaascgra.i $e |- I = ( Itv ` G ) $.
  tgaascgra.l $e |- L = ( LineG ` G ) $.
  tgaascgra.k $e |- K = ( hlG ` G ) $.
  tgaascgra.g $e |- ( ph -> G e. TarskiG ) $.
  tgaascgra.a $e |- ( ph -> A e. P ) $.
  tgaascgra.b $e |- ( ph -> B e. P ) $.
  tgaascgra.c $e |- ( ph -> C e. P ) $.
  tgaascgra.d $e |- ( ph -> D e. P ) $.
  tgaascgra.e $e |- ( ph -> E e. P ) $.
  tgaascgra.f $e |- ( ph -> F e. P ) $.
  tgaascgra.h $e |- ( ph -> H e. P ) $.
  tgaascgra.ncol $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.
  tgaascgra.1 $e |- ( ph -> ( A .- B ) = ( D .- E ) ) $.
  tgaascgra.2 $e
    |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> ) $.
  tgaascgra.3 $e
    |- ( ph -> <" B C A "> ( cgrA ` G ) <" E F D "> ) $.
  tgaascgra.4 $e |- ( ph -> H ( K ` E ) F ) $.
  tgaascgra.5 $e |- ( ph -> ( E .- H ) = ( B .- C ) ) $.

  $( The comparison triangle of the AAS route: with `H` placed on ray `E F` at
     distance `B C` from `E`, the triangle `D E H` is congruent to `A B C`
     ( ~ cgrahl2 then ~ tgsas ), so its angle at `H` can be read off
     ( ~ cgrcgra ) and matched against the given angle at `F`.  The result is
     the angle congruence the case split of ~ tgaas1h consumes. $)
  tgaascgra $p
    |- ( ph -> <" D F E "> ( cgrA ` G ) <" D H E "> )
      $= ( cgracom tgbcne tgacne necomd ccgrg cfv eqid co eqcomd cgrahl2 tgsas
        cgr3simp3 trgcgr cgrcgra cgratr cgraswaplr ) AGHEGFJEIKNOQPTUEUFUDUEUG
         UDAGHECFJDBIGKELOQTSUEUFUDUBUCUAACDBGFHEIKLOQTSUBUCUAUEUFUDUKUNUEUGUD
         ACDBGFJEIKLOQTSUBUCUAUEUGUDABCDFIKMOQRTUAUBUCUHUOABDABCDFIKMOQRTUAUBU
         CUHUPUQACDBGFIURUSZJEINOPVJUTZTUBUCUAUEUGUDAGJNVAZCDNVAZUMVBZABCDEFVJ
         GJIKNOPQVKTUAUBUCUDUEUGABCDEFGJIKNOPQTUAUBUCUDUEUGUIABCDEFGHIKLJOQSTU
         AUBUCUDUEUFUJUGULVCVNVDVEUIVFVGVHVI $.
$}

${
  tgaas1h.p $e |- P = ( Base ` G ) $.
  tgaas1h.m $e |- .- = ( dist ` G ) $.
  tgaas1h.i $e |- I = ( Itv ` G ) $.
  tgaas1h.l $e |- L = ( LineG ` G ) $.
  tgaas1h.k $e |- K = ( hlG ` G ) $.
  tgaas1h.g $e |- ( ph -> G e. TarskiG ) $.
  tgaas1h.a $e |- ( ph -> A e. P ) $.
  tgaas1h.b $e |- ( ph -> B e. P ) $.
  tgaas1h.c $e |- ( ph -> C e. P ) $.
  tgaas1h.d $e |- ( ph -> D e. P ) $.
  tgaas1h.e $e |- ( ph -> E e. P ) $.
  tgaas1h.f $e |- ( ph -> F e. P ) $.
  tgaas1h.h $e |- ( ph -> H e. P ) $.
  tgaas1h.ncol $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.
  tgaas1h.1 $e |- ( ph -> ( A .- B ) = ( D .- E ) ) $.
  tgaas1h.2 $e
    |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> ) $.
  tgaas1h.3 $e
    |- ( ph -> <" B C A "> ( cgrA ` G ) <" E F D "> ) $.
  tgaas1h.4 $e |- ( ph -> H ( K ` E ) F ) $.
  tgaas1h.5 $e |- ( ph -> ( E .- H ) = ( B .- C ) ) $.

  $( ~ tgaas1 with the constructed point `H` still explicit: the case split on
     `F = H`.  Equal, and the side equality is a substitution; distinct, and
     ~ tgaasne closes the branch.  BOTH branches are proved -- assuming `F = H`
     would be assuming the theorem. $)
  tgaas1h $p
    |- ( ph -> ( B .- C ) = ( E .- F ) )
      $= ( co wceq wa eqcomd adantr simpr oveq2d eqtrd wne cstrkg wcel wo wn
        tgdefncol ncolrot1 cfv wbr cs3 ccgra tgaascgra tgaasne pm2.61dane )
         ACDNUNZGHNUNZUOZHJAHJUOZUPZVPGJNUNZVQAVPWAUOVSAWAVPUMUQURVTVQWAVTHJGN
         AVSUSUTUQVAAHJVBZUPVREFGHIJKLMNOPQRSAIVCVDWBTURAEFVDWBUDURAGFVDWBUEUR
         AHFVDWBUFURAJFVDWBUGURAEGHMUNVDGHUOVEVFWBAFIKMEGHORQTUDUEUFABCDEFGHIK
         MNOPQRTUAUBUCUDUEUFUHUJVGVHURAJHGLVIVJWBULURAWBUSAEHGVKEJGVKIVLVIVJWB
         ABCDEFGHIJKLMNOPQRSTUAUBUCUDUEUFUGUHUIUJUKULUMVMURVNVO $.
$}

${
  $( `x` is the point copied onto ray `E F`, a proof-internal dummy of
     ~ tgaas1 : mandatory $d. $)
  $d ph x $.  $d P x $.   $d .- x $.  $d I x $.  $d L x $.  $d G x $.
  $d A x $.   $d B x $.   $d C x $.   $d D x $.  $d E x $.  $d F x $.

  tgaas.p $e |- P = ( Base ` G ) $.
  tgaas.m $e |- .- = ( dist ` G ) $.
  tgaas.i $e |- I = ( Itv ` G ) $.
  tgaas.l $e |- L = ( LineG ` G ) $.
  tgaas.g $e |- ( ph -> G e. TarskiG ) $.
  tgaas.a $e |- ( ph -> A e. P ) $.
  tgaas.b $e |- ( ph -> B e. P ) $.
  tgaas.c $e |- ( ph -> C e. P ) $.
  tgaas.d $e |- ( ph -> D e. P ) $.
  tgaas.e $e |- ( ph -> E e. P ) $.
  tgaas.f $e |- ( ph -> F e. P ) $.
  tgaas.ncol $e |- ( ph -> -. ( C e. ( A L B ) \/ A = B ) ) $.
  tgaas.1 $e |- ( ph -> ( A .- B ) = ( D .- E ) ) $.
  tgaas.2 $e |- ( ph -> <" A B C "> ( cgrA ` G ) <" D E F "> ) $.
  tgaas.3 $e |- ( ph -> <" B C A "> ( cgrA ` G ) <" E F D "> ) $.

  $( Under the AAS hypotheses, the side included between the two given angles
     is congruent.  This is the whole content of AAS: ~ tgaas simply packages
     it with SAS ( ~ tgsas ).  The point copied onto ray `E F` by ~ tgaascgra
     is eliminated here. $)
  tgaas1 $p
    |- ( ph -> ( B .- C ) = ( E .- F ) )
      $= ( vx cv chlg cfv wbr co wceq wa wcel eqid cstrkg adantr simpl simprd
        wo wn cs3 ccgra simpr simpld tgaas1h tgdefncol tgbcne necomd hlcgrex
        r19.29a ) AUHUIZHGIUJUKZUKZULZGVNLUMZCDLUMZUNZUOZVSGHLUMUNUHFAVNFUPZUO
         ZWAUOZBCDEFGHIVNJVOKLMNOPVOUQZWCIURUPZWAAWFWBQUSUSWCBFUPZWAAWGWBRUSUS
         WCCFUPZWAAWHWBSUSUSWCDFUPZWAAWIWBTUSUSWCEFUPZWAAWJWBUAUSUSWCGFUPZWAAW
         KWBUBUSUSWCHFUPZWAAWLWBUCUSUSWDAWBWCWAUTVAWCDBCKUMZUPZBCUNZVBZVCZWAAW
         QWBUDUSUSWCBCLUMZEGLUMZUNZWAAWTWBUEUSUSWCBCDVDZEGHVDZIVEUKZULZWAAXDWB
         UFUSUSWCCDBVDZGHEVDZXCULZWAAXGWBUGUSUSWDVQVTWCWAVFZVGWDVQVTXHVAVHAUHG
         CDHFIJVOLMOWEUBSTQUCNAGHAEGHFIJKMOPQUAUBUCABCDEFGHIJKLMNOPQRSTUAUBUCU
         DUFVIVJVKABCDFIJKMOPQRSTUDVJVLVM $.

  $( Angle-angle-side: two triangles with two congruent angles and a congruent
     side not included between them are congruent.  The side included between
     the two angles is congruent by ~ tgaas1 , which reduces the theorem to
     SAS ( ~ tgsas ). $)
  tgaas $p
    |- ( ph -> <" A B C "> ( cgrG ` G ) <" D E F "> )
      $= ( tgaas1 tgsas ) ABCDEFGHIJLMNOQRSTUAUBUCUEUFABCDEFGHIJKLMNOPQRSTUAUB
         UCUDUEUFUGUHUI $.
$}
