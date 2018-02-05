Require Import Lib Pip_state Pip_stateLib List.
Require Import  Omega List Coq.Logic.ProofIrrelevance.
Import List.ListNotations. 

(** THE VERTICAL SHARING PROPERTY: 
    All child used pages (configuration tables and mapped pages) are mapped into 
    the parent partition  *)
Definition verticalSharing s : Prop := 

forall parent child : page , 

  In parent (getPartitions multiplexer s) -> 

  In child (getChildren parent s) ->  

  incl (getUsedPages child s) (getMappedPages parent s).

(** THE ISOLATION PROPERTY BETWEEN PARTITIONS, 
    If we take two different children of a given parent, 
    so all their used pages are different  *)
Definition partitionsIsolation  s : Prop :=  

forall parent child1 child2 : page , 

  In parent (getPartitions multiplexer s)-> 

  In child1 (getChildren parent s) -> 

  In child2 (getChildren parent s) -> 

  child1 <> child2 ->

  disjoint (getUsedPages child1 s)(getUsedPages child2 s).

(** THE ISOLATION PROPERTY BETWEEN THE KERNEL DATA AND PARTITIONS
    kernel data is the configuration pages of partitions.
    All configuration tables of a given partition are inaccessible by all
    partitions *)
Definition kernelDataIsolation s : Prop :=

forall partition1 partition2, 

  In partition1 (getPartitions multiplexer s) ->

  In partition2 (getPartitions multiplexer s) -> 

  disjoint (getAccessibleMappedPages partition1 s) (getConfigPages partition2 s).


(** ** The [dataStructurePdSh1Sh2asRoot] property defines the type of different values 
stored into the page directory structure, the first shadow structure and 
the second shadow structure.
Configuation tables of the last level must contain :
 - Physical entries (the type [PEntry] is already definded in [Model.ADT]) for the page directory 
  data structure 
 - Virtual entries (the type [VEntry] is already definded in [Model.ADT] ) for the first shadow 
   data structure
 - Virtual addresses (the type [vaddr] is already definded in [Model.ADT]) for the second shadow 
  data structure
The other tables contain Physical entries  
    [idxroot] should be PDidx, sh1idx or sh2idx.
 (1)   
*)
Definition dataStructurePdSh1Sh2asRoot (idxroot : index) (s : state) :=
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall entry, nextEntryIsPP partition idxroot entry s ->  
forall va : vaddr, 
True -> forall level stop , Some level = getNbLevel -> 
forall indirection idx, getIndirection entry va level stop s = Some indirection -> 
( indirection = defaultPage \/ 
(( ( stop < level /\ isPE indirection idx s )\/  
   ( stop >= level /\ ( (isVE indirection idx s /\ idxroot = sh1idx) \/ 
                       (isVA indirection idx s /\ idxroot = sh2idx) \/ 
                       (isPE indirection idx s /\ idxroot = PDidx) ) ))
                       /\ 
  indirection <> defaultPage)) .

Definition wellFormedFstShadow (s : state) :=
forall partition,
In partition (getPartitions multiplexer s) -> 
forall va pg pd sh1,
getPd partition (memory s) = Some pd -> 
getFstShadow partition (memory s) = Some sh1 ->
getMappedPage pd s va= Some pg ->       
exists vainparent, getVirtualAddressSh1 sh1 s va = Some vainparent. 

Definition wellFormedSndShadow (s : state) :=
forall partition,
In partition (getPartitions multiplexer s) -> 
partition <> multiplexer -> 
forall va pg pd sh2,
getPd partition (memory s) = Some pd -> 
getSndShadow partition (memory s) = Some sh2 ->
getMappedPage pd s va= Some pg ->       
exists vainparent, getVirtualAddressSh2 sh2 s va = Some vainparent /\
beqVAddr defaultVAddr vainparent = false . 

Definition wellFormedShadows (idxroot : index) (s : state) :=
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall pdroot , 
getPd partition (memory s) = Some pdroot -> 
forall structroot, nextEntryIsPP partition idxroot structroot s ->  
forall nbL stop , Some nbL = getNbLevel -> 
forall indirection1  va, 
getIndirection pdroot va nbL stop s = Some indirection1 ->
(defaultPage =? indirection1) = false -> 
(exists indirection2, 
getIndirection structroot va nbL stop s = Some indirection2 /\ 
(defaultPage =? indirection2) = false).  

(* Definition fstShadowWellFormed (s : state) :=
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall pdroot sh1Root, 
StateLib.getPd partition (memory s) = Some pdRoot -> 
StateLib.getFstShadow partition (memory s) = Some sh1Root ->
forall level stop , Some level = getNbLevel -> 
forall indirection1 indirection2 va, 
getIndirection pdRoot va level stop s = Some defaultPage ->
getIndirection sh1Root va level stop s = Some defaultPage.  *)

(** ** The [currentPartitionInPartitionsList] property specifies that the 
    current partition must be into the list of partitions retrieved from the 
    first created partition (multiplexer) 
    (2) *)
Definition currentPartitionInPartitionsList (s : state) := 
 In (currentPartition s) (getPartitions multiplexer s).

(** ** The [currentPartitionIsNotDefaultPage t] property specifies that the 
    current partition is not a default physical page  
    (2) *)
Definition currentPartitionIsNotDefaultPage (s : state) :=
 (currentPartition s) <> defaultPage. 
 
(** ** The [parentInPartitionList] property specifies that the parent of a given 
partition should be into the list of partitions retrieved from the 
    first created partition (multiplexer) 
    (3) *)
Definition parentInPartitionList (s : state) := 
forall partition, In partition (getPartitions multiplexer s) -> 
forall parent, nextEntryIsPP partition PPRidx parent s ->
In parent (getPartitions multiplexer s). 

(** ** The [partitionDescriptorEntry] defines some properties of the partition descriptor. 
    - A partition descriptor is a table containing virtual addresses and physical pages.
    - Indecie PDidx, sh1idx, sh2idx, PPRidx and PRidx should be less than ("tableSize" - 1) and 
      contain virtual addresses.
    - The successors of these indices contain physical pages which should not be 
      equal to "defaultPage".
    (4) *)
Definition partitionDescriptorEntry s := 
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall (idxroot : index), (idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx \/ 
idxroot = sh3idx \/
idxroot = PPRidx  \/ idxroot = PRidx ) ->
idxroot < tableSize - 1  /\
isVA partition idxroot  s /\ 
exists entry, nextEntryIsPP partition idxroot entry s  /\  
entry <> defaultPage.

(** ** The [multiplexerWithoutParent] specifies that the multiplexer is the root of
the partition tree *)
Definition multiplexerWithoutParent s :=
getParent multiplexer (memory s) = None.

(** ** The [noDupMappedPagesList] requires that mapped pages of a single partition
    are different 
    (5) *)
Definition noDupMappedPagesList s :=
forall (partition : page),  
In partition (getPartitions multiplexer s) ->  
 NoDup (getMappedPages partition s).
 
(** ** The [noDupConfigPagesList] requires that configuation tables of
    a single partition are different 
    (6) *)
Definition noDupConfigPagesList s :=
forall idxroot, (idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) -> 
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall root, nextEntryIsPP partition idxroot root s->
 NoDup (getIndirections root s). 

(** ** The [accessibleVAIsNotPartitionDescriptor] requires that accessible virtual 
    addresses are not marked as partition descriptor into the first shadow configuation
    structure 
    (7) *)
Definition accessibleVAIsNotPartitionDescriptor s :=
forall partition va pd sh1 page, 
  In partition (getPartitions multiplexer s) -> 
  getPd partition (memory s) = Some pd -> 
  getFstShadow partition (memory s) = Some sh1 -> 
  getAccessibleMappedPage pd s va = Some page -> 
  getPDFlag sh1 va s = false.

(** ** The [accessibleChildPageIsAccessibleIntoParent] requires that all accessible physical 
      pages into a given partition should be accessible into its parent
    (8) *)
Definition  accessibleChildPageIsAccessibleIntoParent s := 
forall partition va pd  accessiblePage, 
  In partition (getPartitions multiplexer s) ->
  getPd partition (memory s) = Some pd ->
  getAccessibleMappedPage pd s va = Some accessiblePage ->
  isAccessibleMappedPageInParent partition va accessiblePage s = true. 

(** ** The [noCycleInPartitionTree] requires that a partition and 
        its ancestors are different 
    (9) **)
Definition noCycleInPartitionTree s := 
forall ancestor partition, 
In partition (getPartitions multiplexer s) -> 
In ancestor (getAncestors partition s) -> 
ancestor <> partition.

(** ** The [configTablesAreDifferent] requires that configuation tables of different
        partitions are disjoint
      (10) **)
Definition configTablesAreDifferent s := 
forall partition1 partition2,
In partition1 (getPartitions multiplexer s) -> 
In partition2 (getPartitions multiplexer s) -> 
partition1 <> partition2 -> 
disjoint (getConfigPages partition1 s) (getConfigPages partition2 s).

(** ** The [isChild] specifies that a given partition should be a child of the 
        physical page stored as parent into the associated partition descriptor 
    (11) **)
Definition isChild  s :=
forall partition parent : page,
In partition (getPartitions multiplexer s) -> 
getParent partition (memory s) = Some parent -> 
In partition (getChildren parent s).


(** ** The [isParent] specifies that if we take any child into the children list of any 
partition into the partition list so this partition should be the parent of this child 
 (..) **)
Definition isParent  s :=
forall partition parent : page,
In parent (getPartitions multiplexer s) -> 
In partition (getChildren parent s) -> 
getParent partition (memory s) = Some parent.

(** ** The [isPresentNotDefaultIff] specifies that if the present flag of a physical 
    entry is equal to false so the associated physical page must be equal to the default 
    value 
    (12) **)
Definition isPresentNotDefaultIff s:=
forall table idx , 
 readPresent table idx (memory s) = Some false <-> 
 readPhyEntry table idx (memory s) = Some defaultPage .

(** ** The [physicalPageNotDerived] specifies that if a given physical
    page is marked as not derived in a parent so it is not mapped in any child
    (13)
**) 
Definition physicalPageNotDerived s := 
forall parent va pdParent pageParent, 
In parent (getPartitions multiplexer s) -> 
getPd parent (memory s) = Some pdParent -> 
~ isDerived parent va s -> 
getMappedPage pdParent s va = Some pageParent -> 
forall child pdChild vaInChild pageChild , 
In child (getChildren parent s) -> 
getPd child (memory s) = Some pdChild -> 
getMappedPage pdChild s vaInChild = Some  pageChild -> 
pageParent <> pageChild.

Definition noDupPartitionTree s :=
NoDup (getPartitions multiplexer s) .

(** ** Conjunction of all consistency properties *)
Definition consistency s := 
 partitionDescriptorEntry s /\  
 dataStructurePdSh1Sh2asRoot PDidx s /\
 dataStructurePdSh1Sh2asRoot sh1idx s /\
 dataStructurePdSh1Sh2asRoot sh2idx s /\
 currentPartitionInPartitionsList s /\
 noDupMappedPagesList s /\
 noDupConfigPagesList s  /\
 parentInPartitionList s /\
 accessibleVAIsNotPartitionDescriptor s /\
 accessibleChildPageIsAccessibleIntoParent s /\
 noCycleInPartitionTree s /\ 
 configTablesAreDifferent s /\ 
 isChild s /\
 isPresentNotDefaultIff s /\
 physicalPageNotDerived s /\
 multiplexerWithoutParent s /\
 isParent s /\
 noDupPartitionTree s /\
 wellFormedFstShadow s /\
 wellFormedSndShadow s /\
 wellFormedShadows sh1idx s /\
 wellFormedShadows sh2idx s /\
 currentPartitionIsNotDefaultPage s .

Definition propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s : Prop :=
partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\
consistency s /\
Some level = getNbLevel /\
false = checkVAddrsEqualityWOOffset nbLevel descChild pdChild level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow2 list level /\
(Kidx =? nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex) = false /\
(Kidx =? nth (length pdChild - (nbLevel - 1 + 2)) pdChild defaultIndex) = false /\
(Kidx =? nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 defaultIndex) = false /\
(Kidx =? nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 defaultIndex) = false /\
(Kidx =? nth (length list - (nbLevel - 1 + 2)) list defaultIndex) = false /\
beqVAddr defaultVAddr pdChild = false /\ 
beqVAddr defaultVAddr shadow1 = false /\
beqVAddr defaultVAddr shadow2 = false /\ 
beqVAddr defaultVAddr list = false /\
currentPart = currentPartition s /\
nextEntryIsPP currentPart PDidx currentPD s /\
(forall idx : index,
getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) /\
(defaultPage =? ptRefChild) = false /\
getIndexOfAddr descChild fstLevel = idxRefChild /\
entryPresentFlag ptRefChild idxRefChild presentRefChild s /\
entryUserFlag ptRefChild idxRefChild accessibleChild s /\
(forall idx : index,
getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) /\
(defaultPage =? ptPDChild) = false /\
getIndexOfAddr pdChild fstLevel = idxPDChild /\
entryPresentFlag ptPDChild idxPDChild presentPDChild s /\
entryUserFlag ptPDChild idxPDChild false s /\
(forall idx : index,
getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) /\
(defaultPage =? ptSh1Child) = false /\
getIndexOfAddr shadow1 fstLevel = idxSh1 /\
entryPresentFlag ptSh1Child idxSh1 presentSh1 s /\
entryUserFlag ptSh1Child idxSh1 accessibleSh1 s /\
(forall idx : index,
getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) /\
(defaultPage =? ptSh2Child) = false /\
getIndexOfAddr shadow2 fstLevel = idxSh2 /\
entryPresentFlag ptSh2Child idxSh2 presentSh2 s /\
entryUserFlag ptSh2Child idxSh2 accessibleSh2 s /\
(forall idx : index,
getIndexOfAddr list fstLevel = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) /\
(defaultPage =? ptConfigPagesList) = false /\
getIndexOfAddr list fstLevel = idxConfigPagesList /\
entryPresentFlag ptConfigPagesList idxConfigPagesList presentConfigPagesList s /\
entryUserFlag ptConfigPagesList idxConfigPagesList accessibleList s /\
nextEntryIsPP currentPart sh1idx currentShadow1 s /\
(forall idx : index,
getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\
getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) /\
(defaultPage =? ptRefChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptRefChildFromSh1 idxRefChild va s /\ beqVAddr defaultVAddr va = derivedRefChild) /\
(forall idx : index,
getIndexOfAddr pdChild fstLevel = idx ->
isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) /\
(defaultPage =? ptPDChildSh1) = false /\
(exists va : vaddr,
isEntryVA ptPDChildSh1 idxPDChild va s /\ beqVAddr defaultVAddr va = derivedPDChild) /\
(forall idx : index,
getIndexOfAddr shadow1 fstLevel = idx ->
isVE ptSh1ChildFromSh1 idx s /\
getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) /\
(defaultPage =? ptSh1ChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) /\
(forall idx : index,
getIndexOfAddr shadow2 fstLevel = idx ->
isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) /\
(defaultPage =? childSh2) = false /\
(exists va : vaddr,
isEntryVA childSh2 idxSh2 va s /\ beqVAddr defaultVAddr va = derivedSh2Child) /\
(forall idx : index,
getIndexOfAddr list fstLevel = idx ->
isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s) /\
(defaultPage =? childListSh1) = false /\
(exists va : vaddr,
isEntryVA childListSh1 idxConfigPagesList va s /\
beqVAddr defaultVAddr va = derivedRefChildListSh1) /\
isEntryPage ptPDChild idxPDChild phyPDChild s /\
(defaultPage =? phyPDChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) /\
isEntryPage ptSh1Child idxSh1 phySh1Child s /\
(defaultPage =? phySh1Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) /\
isEntryPage ptSh2Child idxSh2 phySh2Child s /\
(defaultPage =? phySh2Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) /\
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s /\
(defaultPage =? phyConfigPagesList) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) /\
isEntryPage ptRefChild idxRefChild phyDescChild s /\ (defaultPage =? phyDescChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) -> ~ In phyDescChild (getConfigPages partition s)) /\
isPartitionFalse ptSh1ChildFromSh1 idxSh1 s /\
isPartitionFalse childSh2 idxSh2 s /\
isPartitionFalse childListSh1 idxConfigPagesList s /\
isPartitionFalse ptRefChildFromSh1 idxRefChild s /\
isPartitionFalse ptPDChildSh1 idxPDChild s .


Definition propagatedPropertiesAddVaddr s (vaInCurrentPartition vaChild: vaddr)  currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level
:=
(partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\ 
consistency s /\
(Kidx =? nth (length vaInCurrentPartition - (nbLevel - 1 + 2)) vaInCurrentPartition defaultIndex) = false /\
(Kidx =? nth (length vaChild - (nbLevel - 1 + 2)) vaChild defaultIndex) = false /\
currentPart = currentPartition s /\
Some level = getNbLevel /\
nextEntryIsPP currentPart sh1idx currentShadow s /\
getIndexOfAddr descChild fstLevel = idxDescChild /\
isVE ptDescChild (getIndexOfAddr descChild fstLevel) s /\
getTableAddrRoot ptDescChild sh1idx currentPart descChild s /\ (defaultPage =? ptDescChild) = false /\
entryPDFlag ptDescChild idxDescChild true s /\
isVE ptVaInCurPart (getIndexOfAddr vaInCurrentPartition fstLevel) s /\
getTableAddrRoot ptVaInCurPart sh1idx currentPart vaInCurrentPartition s /\
(defaultPage =? ptVaInCurPart) = false /\
getIndexOfAddr vaInCurrentPartition fstLevel = idxvaInCurPart /\
isEntryVA ptVaInCurPart idxvaInCurPart vainve s /\
beqVAddr defaultVAddr vainve = isnotderiv /\
nextEntryIsPP currentPart PDidx currentPD s /\
isPE ptVaInCurPartpd (getIndexOfAddr vaInCurrentPartition fstLevel) s /\
getTableAddrRoot ptVaInCurPartpd PDidx currentPart vaInCurrentPartition s /\
(defaultPage =? ptVaInCurPartpd) = false /\
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s /\
entryPresentFlag ptVaInCurPartpd idxvaInCurPart presentmap s /\
isPE ptDescChildpd (getIndexOfAddr descChild fstLevel) s /\
getTableAddrRoot ptDescChildpd PDidx currentPart descChild s /\
(defaultPage =? ptDescChildpd) = false /\
getIndexOfAddr descChild fstLevel = idxDescChild1 /\
entryPresentFlag ptDescChildpd idxDescChild1 presentDescPhy s /\
isEntryPage ptDescChildpd idxDescChild1 phyDescChild s /\
In phyDescChild (getChildren (currentPartition s) s) /\
nextEntryIsPP phyDescChild PDidx pdChildphy s /\
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s /\
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s /\
(defaultPage =? ptVaChildpd) = false /\
getIndexOfAddr vaChild fstLevel = idxvaChild /\
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s /\
isEntryPage ptVaInCurPartpd idxvaInCurPart phyVaChild s /\
nextEntryIsPP phyDescChild sh2idx sh2Childphy s) /\
isVA ptVaChildsh2 (getIndexOfAddr vaChild fstLevel) s /\
getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s /\
(defaultPage =? ptVaChildsh2) = false.
