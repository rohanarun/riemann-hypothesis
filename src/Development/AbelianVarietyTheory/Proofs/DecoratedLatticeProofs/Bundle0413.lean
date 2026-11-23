module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemChainLevelIffCarriesLatticeOffLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LevChain

theorem mem_levS_iff_moves : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (j : ℕ) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), s.Is c j → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ c.S → ∀ κ ∈ grpAt s.V (· = v), κ ∈ levS s.V s.β s.L ↔ Moves s.V κ s.Λ s.Λ (· = v) := by
  intro D c j s hs v hv κ hκ
  haveI : Submodule.IsLattice D.host.E s.Λ := hs.selfDual.1
  have hfg : s.Λ.FG := Submodule.IsLattice.fg (A := D.host.E) s.Λ
  have hGf := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff s.V (· = v) κ).1 hκ
  have hSt : Lev.finE s.V κ ∈ Formalism.L2.DIV.St s.β ↔ κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig s.V.gram s.Λ := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg s.V s.β s.Λ hs.frame hfg κ]
    exact GlobalTheory.AdelicU.mem_levelOpen.symm
  constructor
  · intro h
    have h2 : Lev.finE s.V κ ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L := h.2
    exact GlobalTheory.FinPl.KOpen.moves_of_levelOpen s.V s.Λ hfg _ (hSt.1 (Formalism.L2.DIV.parLev_St h2.1))
  · intro hm
    have hS := hSt.2 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK s.V s.Λ hfg _ ⟨hκ, hm⟩)
    obtain ⟨hr, ξ, hL⟩ := hs.lev
    refine ⟨hGf.1, ?_⟩
    refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS fun PP hPP => ?_
    have hPg : PP ∈ c.Pg := by
      rw [hL] at hPP
      simpa [Lev.datY] using hPP
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β κ PP hS (hGf.2 _ ?_)
    intro he
    exact hv (Finset.mem_image.2 ⟨PP, hPg, he⟩)

end GlobalTheory.Core.Mi.LevChain

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemColGroupIff
section
noncomputable section

namespace GlobalTheory.SeeSaw.LevMem

section Columns

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.LevRead GlobalTheory.Mem.Col2.TC.GLev0 Matrix
open scoped TensorProduct

section Pts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsInt (m : GL (Fin n) (AfE F E)) : Prop := (∀ i j, m.1 i j ∈ RInt F E) ∧ ∀ i j, (m⁻¹).1 i j ∈ RInt F E

theorem isInt_of {m : GL (Fin n) (AfE F E)} (h : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (m.1 *ᵥ z) i ∈ RInt F E) :
    IsInt m := by
  have h1 : ∀ j i, (Pi.single j 1 : Fin n → AfE F E) i ∈ RInt F E := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => by simpa using (h _).1 (h1 j) i, fun i j => ?_⟩
  have := (h ((m⁻¹).1 *ᵥ Pi.single j 1)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact h1 j) i
  simpa using this

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

end Pts

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end Columns

section LocalField

open ValuativeRel IsLocalRing Matrix GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos Reduces)

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

end LocalField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge

section Adelic

variable {D : D7}

theorem mem_latHat_iff {n : ℕ} {L : Set (Fin n → D.host.E)} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D n)
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) : z ∈ latHat D.host.F D.host.E L ↔ ∀ i, z i ∈ intAE D := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (hL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (hL _).2 fun j => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [x.isIntegral_coe, isIntegral_zero]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy


set_option maxHeartbeats 1000000 in
theorem moves_iff {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D V.rank) {κ : GA D V} {n : ℕ} (hn : V.rank = n)
    {y : GL (Fin n) (EF D)} (hy : finM V hn κ = y.1) :
    GlobalTheory.FinPl.Moves V κ L L (fun _ => True) ↔ IsInt (F := D.host.F) (E := D.host.E) y := by
  subst hn
  have h1 : ∀ a : Fin V.rank → AE D, (∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True) →
      (a ∈ GlobalTheory.FinPl.latV V L (fun _ => True) ↔ ∀ i, toEAf D (a i) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E) := fun a ha =>
    (GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ a ha).trans ((mem_latHat_iff hL _).trans
      (forall_congr' fun i => GlobalTheory.IdemSupport.mem_intAE_iff _))
  have h2 : ∀ (a : Fin V.rank → AE D) i, toEAf D ((mt V κ *ᵥ a) i) = (y.1 *ᵥ fun j => toEAf D (a j)) i := fun a i => by
    rw [← hy]
    exact RingHom.map_mulVec (toEAf D) _ a i
  constructor
  · intro h
    refine isInt_of fun z => ?_
    let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
    choose a ha ha' using fun i => GlobalTheory.KStabBridge.exists_fin_lift (D := D) (sw.symm (z i))
    have hz : ∀ i, toEAf D (a i) = z i := fun i => (congrArg sw (ha' i)).trans (sw.apply_symm_apply _)
    have hi : ∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True := fun i =>
      Submodule.mem_inf.2 ⟨ha i, (Submodule.mem_iInf _).2 fun u => absurd trivial u.2⟩
    have := h a hi
    rw [h1 a hi, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ hi)] at this
    simp only [h2, hz] at this
    exact this
  · intro h a ha
    rw [h1 a ha, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ ha)]
    simp only [h2]
    refine ⟨PtExist.mulVec_int h.1, fun h' i => ?_⟩
    have := PtExist.mulVec_int h.2 h' i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

section Split

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

end Split

variable {u : D.what₂.Word} {a : XPart D u}

end Adelic

end GlobalTheory.SeeSaw.LevMem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemScaledLatticeCompletionIffPolarisationInverse
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf D.host.F) * 0 = 0
    rw [zero_mul]
  · rfl

theorem pair_tmul_mul (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul]

def Good (v : Pl D) (α : Af D.host.F) : Prop :=
  α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w α = 0

theorem Good.mul {v : Pl D} {α β : Af D.host.F} (hα : Good v α) (hβ : Good v β) : Good v (α * β) :=
  ⟨fun w => by rw [map_mul]; exact mul_mem (hα.1 w) (hβ.1 w), fun w hw => by rw [map_mul, hα.2 w hw, zero_mul]⟩

theorem good_indP (v : Pl D) : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]

theorem indicatorAdele_mul_self (v : Pl D) :
    GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v) = GlobalTheory.SelfDualAt.indP (D := D) (· = v) := by
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  have h1 : evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v)) =
      evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
    rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs <;> simp
  exact h1

theorem gen_mem_idAt (v : Pl D) (α : Af D.host.F) (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hα _ w.2, TensorProduct.zero_tmul]

theorem AA_ne_zero : D.host.AA ≠ 0 :=
  (GlobalTheory.SeeSaw.LiftModel.AA_ne (D := D) Formalism.IndefR.Fin.factPrincipalDatum).1

theorem int_of_mem {c d : D.host.E} (hc : c ∈ D.host.AA) (hd : d ∈ D.host.AA⁻¹) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = d * c := by
  have h : d * c ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hd hc
  rw [inv_mul_cancel₀ AA_ne_zero] at h
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨o, ho⟩

theorem smul_latV_mem_latA (S : HSp D) (L : Lat S) (v : Pl D) {ε : Af D.host.F} (hε : Good v ε) {c : D.host.E}
    (hc : c ∈ D.host.AA) {z : Fin S.rank → AE D} (hz : z ∈ latV S L (· = v)) :
    ((pairA D.host.F 0 ε) ⊗ₜ[D.host.F] c : AE D) • z ∈ latA S L (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hz
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβ1, hβ2, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    apply AddSubgroup.subset_closure
    have g := hε.mul ⟨hβ1, hβ2⟩
    refine ⟨ε * β, g.1, g.2, c, hc, x, hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.LatAt

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem mem_latA_fwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hy : y ∈ latA S L (· = v)) :
    (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα1, hα2, c, hc, x, hx, rfl⟩ := hy
    refine ⟨fun i => gen_mem_idAt v α hα2 _, fun s hs => ?_⟩
    unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ1, hβ2, d, hd, rfl⟩ := hs
      obtain ⟨o, ho⟩ := int_of_mem hc hd
      unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
      apply AddSubgroup.subset_closure
      have g := Good.mul (v := v) ⟨hβ1, hβ2⟩ ⟨hα1, hα2⟩
      refine ⟨β * α, g.1, g.2, 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul, Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
      congr 2
      exact ho.symm
    | zero => rw [zero_smul]; exact zero_mem _
    | add s t _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ h1 h2 =>
    exact ⟨fun i => add_mem (h1.1 i) (h2.1 i), fun s hs => by rw [smul_add]; exact add_mem (h1.2 s hs) (h2.2 s hs)⟩
  | neg y _ h => exact ⟨fun i => neg_mem (h.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (h.2 s hs)⟩

theorem mem_latA_bwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hsupp : ∀ i, y i ∈ idAt D (· = v))
    (h : ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v)) : y ∈ latA S L (· = v) := by
  have hε : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := good_indP v
  have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹,
      ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] t : AE D) • y ∈ latA S L (· = v) := by
    intro t ht
    refine FractionalIdeal.mul_induction_on ht ?_ ?_
    · intro c hc d hd
      have e : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (c * d) : AE D) =
          ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] c) *
            ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] d) := by
        rw [pair_tmul_mul, indicatorAdele_mul_self]
      rw [e, mul_smul]
      refine smul_latV_mem_latA S L v hε hc (h _ ?_)
      unfold idV
      exact AddSubgroup.subset_closure ⟨_, hε.1, hε.2, d, hd, rfl⟩
    · intro a b ha hb
      rw [TensorProduct.tmul_add, add_smul]
      exact add_mem ha hb
  have h1 := key 1 (by rw [mul_inv_cancel₀ AA_ne_zero]; exact FractionalIdeal.one_mem_one _)
  have e1 : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) (y i) (hsupp i)
  rwa [e1] at h1

end GlobalTheory.SeeSaw.LatAt

theorem GlobalTheory.SeeSaw.mem_latA_iff_mul_inv : ∀ (D : D7) (v : Pl D) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) :=
  fun _ v S L y => ⟨GlobalTheory.SeeSaw.LatAt.mem_latA_fwd S L v y, fun h => GlobalTheory.SeeSaw.LatAt.mem_latA_bwd S L v y h.1 h.2⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSecondModelStabilizerIffCarriesRowLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KsetAt

theorem mem_Kset_iff_moves : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (κ : GA D (D.sp.Y 0)), κ ∈ grpAt (D.sp.Y 0) (· = v) → ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v)) := by
  intro D X h v κ hκ
  have hlat : Submodule.IsLattice D.host.E (latS D) :=
    GlobalTheory.StdFrames.isLattice_crdLat (D.sp.Y 0) (D.sp.Y 0).standardTuple_isLattice
  obtain ⟨β, hβ⟩ := GlobalTheory.StdFrames.exists_base (D.sp.Y 0)
  have hβ' : Formalism.L2.DIV.IsFrame β (latS D) := by
    change Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)
    rw [hβ]
    exact GlobalTheory.StdFrames.isFrame_lat β
  have h1 := ((GlobalTheory.SeeConjReadIota.read_iota X h β hβ' κ).2.1)
  have h2 := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg (D.sp.Y 0) β (latS D) hβ' hlat.fg κ
  have h3 : κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig (D.sp.Y 0).gram (latS D) ↔
      Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v) :=
    ⟨fun hk => GlobalTheory.FinPl.KOpen.moves_of_levelOpen (D.sp.Y 0) (latS D) hlat.fg (· = v) hk,
     fun hm => GlobalTheory.FinPl.KOpen.levelOpen_of_inK (D.sp.Y 0) (latS D) hlat.fg (· = v) ⟨hκ, hm⟩⟩
  exact h1.trans (h2.trans (GlobalTheory.AdelicU.mem_levelOpen.symm.trans h3))

end GlobalTheory.Core.Mi.KsetAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStepMem

theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ m : ℕ, ‖z ^ (2 ^ m) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | (apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt ..)

end GlobalTheory.TriStepMem

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem mem_space_of_typed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (f : GA D S.B'.V → ℂ), IsContAut S.B'.V f → Q.Typed f → f ∈ GlobalTheory.TriStep.space Q := by
  intro D ψ σ S Q f hf hT
  have hgl : Continuous Q.gl₂ := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂).1.continuous
  refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, ?_⟩
  · simp only [rTrans]
    rw [mul_assoc, hf.1 γ hγ]
  · exact hf.2.comp (continuous_id.mul continuous_const)
  · by_cases h0 : ∃ x, f x ≠ 0
    · obtain ⟨x, hx⟩ := h0
      have hval : ∀ j : Q.L₂.J, f (x * Q.gl₂ j.1) = (Q.L₂.lam j : ℂ) * f x := fun j => by
        have := congrFun (hT j) x
        simpa [rTrans] using this
      let φ : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → ℂ := fun g => f (x * Q.gl₂ g) / f x
      have hφc : Continuous φ := (hf.2.comp (continuous_const.mul hgl)).div_const _
      have hφ : ∀ j : Q.L₂.J, φ j.1 = (Q.L₂.lam j : ℂ) := fun j => by
        simp only [φ, hval j]; field_simp
      let U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := (Q.L₂.J : Set _) ∩ φ ⁻¹' Metric.ball 1 (1 / 2)
      have hU : U ∈ nhds (1 : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := by
        refine (Q.co₂.1.inter (Metric.isOpen_ball.preimage hφc)).mem_nhds ⟨Q.L₂.J.one_mem, ?_⟩
        have := hφ 1
        simp only [OneMemClass.coe_one, map_one, Units.val_one] at this
        simp [this]
      obtain ⟨K, hKo, hKU, -, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset Q.k (Q.n₂ ⊕ Fin (Q.c + 1)) U hU
      refine ⟨K, hKo, fun u hu => ?_⟩
      have huJ : u ∈ Q.L₂.J := (hKU hu).1
      have hlam : (Q.L₂.lam ⟨u, huJ⟩ : ℂ) = 1 := by
        apply GlobalTheory.TriStepMem.eq_one_of_pow_two_pow
        intro m
        have hm : u ^ (2 ^ m) ∈ K := K.pow_mem hu _
        have hmU := hKU hm
        have hmJ : u ^ (2 ^ m) ∈ Q.L₂.J := hmU.1
        have e : (⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) = (⟨u, huJ⟩ : Q.L₂.J) ^ (2 ^ m) := rfl
        have h2 : φ (u ^ (2 ^ m)) ∈ Metric.ball (1 : ℂ) (1 / 2) := hmU.2
        rw [show u ^ (2 ^ m) = ((⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) : GL _ _) from rfl, hφ, e, map_pow,
          Units.val_pow_eq_pow_val, Metric.mem_ball, dist_eq_norm] at h2
        exact h2
      have := hT ⟨u, huJ⟩
      rw [hlam, one_smul] at this
      exact this
    · push_neg at h0
      refine ⟨⊤, isOpen_univ, fun u _ => ?_⟩
      funext g
      simp [rTrans, h0]

end GlobalTheory.TriStep
end
end

