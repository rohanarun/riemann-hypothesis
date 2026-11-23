module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionSumProdLastVertexMovedEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDoubleCosetPointsChainPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPassPlaceModelsLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumDatumTrivialCombinationLargeDepth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem lat_col (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl)
    (x : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D)))) :
    actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔
      x ∈ stdLat S (.top t (lastIx D)) :=
  GlobalTheory.LastColLat.colPt_inv_mem_stdLat_iff S ht k hk x

theorem lat_row (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl)
    (x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T))) :
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) :=
  GlobalTheory.LastRowLat.rowPt_mem_stdLat S ht k hk x

theorem vac_col (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    (hlat : ∀ x, actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔ x ∈ stdLat S (.top t (lastIx D))) :
    ∃ c : ℂ, colShift S t g (S.Z.vac (.top t (lastIx D))) = c • S.Z.vac (.top t (lastIx D)) :=
  GlobalTheory.LastVertexVac.colShift_vac_eq_smul S t g hlat

theorem vac_row (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m))
    (hlat : ∀ x, actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔
      x ∈ stdLat S (.chi (lastIx D) D.R.m)) :
    ∃ c : ℂ, rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = c • S.Z.vac (.chi (lastIx D) D.R.m) :=
  GlobalTheory.LastRowVac.vac_row_scalar S k hlat

theorem sb_std (S : GridChoice W U) {t : T} (ht : t ∈ U) {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p)
    (hP : d.P = locPl G t) : IsSBHalf d.e (stdLat S p) d.fn :=
  GlobalTheory.LastVertexMove.isSBHalf_stdLat S ht hp d hP

theorem loc (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (ht : t ∈ U) (hβ : β ∈ S.supp t Φ) (hexp : S.IsExpansion t Φ β τ)
    (hvec : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (k : FinPt G (.grid D.R.m D.R.m)) (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) (cc cr : ℂ)
    (hcc : colShift S t (finEmb G.sp.topDec k) (S.Z.vac (.top t (lastIx D))) = cc • S.Z.vac (.top t (lastIx D)))
    (hcr : rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = cr • S.Z.vac (.chi (lastIx D) D.R.m))
    (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => (d.1 j).fn) (lastIx D)
        (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j (x j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i (y i)) =
    τ.sum fun d a => a * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i) :=
  _root_.GlobalTheory.LastVertexLoc.sum_prod_moved_eq S hL hde hc ht hβ hexp hvec k hk cc cr hcc hcr x y

end GlobalTheory.LastVertexTensor

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vec_eq_model (S : GridChoice W U) {t : T} {p : Pair T} (d : FinDatum G t p) (h : S.Z.HasVec d) (hz : d.z = 1)
    (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hT : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (stdLat S p) 1 (S.Z.vac p) Tm) : S.Z.vec d = Tm d.fn := by
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf, hz, Prod.mk_one_one, map_one, Module.End.one_apply]
  exact hf.2 Tm hT

theorem selfDual_std (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) :
    IsSelfDualC (G.pS p) (S.N.latS p) ∧ IsSelfDualC (G.pT p) (S.N.latT p) := by
  have key : ∀ X, DefNode D.R.m X → IsSelfDualC (G.V X) (colLat (S.N.fr X)) := fun X hX =>
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on X hX)
  have hn := hp.nodes
  cases p with
  | chi i j => exact ⟨isSelfDualC_neg (key _ hn.2), key _ hn.1⟩
  | mu _ i j => exact (by simp [DefPair] at hp)
  | core i => exact (by simp [DefPair] at hp)
  | top _ j => exact ⟨key _ hn.1, key _ hn.2⟩

theorem om_model (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) (hIn : p.InRange D.R.m) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hT : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S p) 1 (S.Z.vac p) Tm) (q : GA D (G.pS p) × GA D (G.pT p))
    (c : ℂ) (hlat : ∀ x, actO _ _ q.1⁻¹ q.2⁻¹ x ∈ stdLat S p ↔ x ∈ stdLat S p) (heig : W.om p q (S.Z.vac p) = c • S.Z.vac p)
    (Φ : WO (G.pS p) (G.pT p) → ℂ) (hΦ : IsSBHalf e (stdLat S p) Φ) : W.om p q (Tm Φ) = c • Tm (moveFn q Φ) := by
  have hind : (fun x => halfInd e (stdLat S p) (actO _ _ q.1⁻¹ q.2⁻¹ x)) = (1 : ℂ) • halfInd e (stdLat S p) := by
    funext x
    rw [Pi.smul_apply, one_smul]
    unfold halfInd
    by_cases h : x ∈ stdLat S p ∧ IsHalf e x
    · rw [if_pos ((and_congr (hlat x) (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _)).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((and_congr (hlat x) (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _)).1 h')), if_neg h]
  have hc : W.om p (q.1, q.2) (S.Z.vac p) = c • Tm (fun x => halfInd e (stdLat S p) (actO _ _ q.1⁻¹ q.2⁻¹ x)) := by
    rw [hind, hT.vac, Prod.mk.eta]
    exact heig
  have := GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ (W.om p) (S.N.latS p) (S.N.latT p) e (S.Z.vac p) Tm (W.om_is p hIn)
    (selfDual_std S hp).1 (selfDual_std S hp).2 (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    (S.Z.vac_is p hp).2.theta hT q.1 q.2 c hc Φ hΦ
  rw [Prod.mk.eta] at this
  exact this

end GlobalTheory.LastVertexTensor

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

def prodForm {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (B : ∀ j, (Y j → ℂ) →ₗ[ℂ] (Y j → ℂ)) (x : ∀ i, X i) (y : ∀ j, Y j) :
    MultilinearMap (RingHom.id ℂ) (fun i => (⊤ : Submodule ℂ (X i → ℂ)))
      (MultilinearMap (RingHom.id ℂ) (fun j => (⊤ : Submodule ℂ (Y j → ℂ))) ℂ) :=
  ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun i =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : X i => ℂ) (x i)) ∘ₗ A i ∘ₗ (⊤ : Submodule ℂ (X i → ℂ)).subtype).smulRight
    ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap fun j =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : Y j => ℂ) (y j)) ∘ₗ B j ∘ₗ (⊤ : Submodule ℂ (Y j → ℂ)).subtype)

theorem prodForm_apply {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (B : ∀ j, (Y j → ℂ) →ₗ[ℂ] (Y j → ℂ)) (x : ∀ i, X i) (y : ∀ j, Y j)
    (f : ∀ i, (⊤ : Submodule ℂ (X i → ℂ))) (g : ∀ j, (⊤ : Submodule ℂ (Y j → ℂ))) :
    prodForm A B x y f g = (∏ i, A i (f i) (x i)) * ∏ j, B j (g j) (y j) := by
  simp [prodForm, MultilinearMap.smulRight_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem productFn_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D)
        (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D)))) j (w j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) i (v i)) =
    τ.sum fun d a => a * (∏ j, S.Z.vec (d.1 j) (w j)) * ∏ i, S.Z.vec (d.2 i) (v i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hexp hvec k hk w v
  obtain ⟨e, he, hdat, -⟩ := id hexp
  obtain ⟨cc, hcc⟩ := vac_col S t (finEmb G.sp.topDec k) (lat_col S ht k hk)
  obtain ⟨cr, hcr⟩ := vac_row S k (lat_row S ht k hk)
  have hloc := loc S hL hde hc ht hβ hexp hvec k hk cc cr hcc hcr
  rcases τ.support.eq_empty_or_nonempty with h0 | ⟨d₀, hd₀⟩
  · simp [Finsupp.sum, h0]
  have hTc : ∀ j : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S (.top t j)) 1
      (S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).1 j
    have h1 := hf.1
    rw [((hdat d₀ hd₀).1 j).2.1] at h1
    exact h1
  have hTr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S (.chi i D.R.m)) 1
      (S.Z.vac (.chi i D.R.m)) Tm := by
    intro i
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).2 i
    have h1 := hf.1
    rw [((hdat d₀ hd₀).2 i).2.1] at h1
    exact h1
  choose Tc hTc using hTc
  choose Tr hTr using hTr
  have hvc : ∀ d ∈ τ.support, ∀ j, S.Z.vec (d.1 j) = Tc j (d.1 j).fn := fun d hd j =>
    vec_eq_model S (d.1 j) ((hvec d hd).1 j) ((hdat d hd).1 j).2.2 (Tc j) (by rw [((hdat d hd).1 j).2.1]; exact hTc j)
  have hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn := fun d hd i =>
    vec_eq_model S (d.2 i) ((hvec d hd).2 i) ((hdat d hd).2 i).2.2 (Tr i) (by rw [((hdat d hd).2 i).2.1]; exact hTr i)
  have hsc : ∀ d ∈ τ.support, colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D))) =
      Tc (lastIx D) (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) := by
    intro d hd
    have hsb := sb_std S ht (defPair_top t (lastIx D)) (d.1 (lastIx D)) ((hdat d hd).1 (lastIx D)).1
    rw [((hdat d hd).1 (lastIx D)).2.1] at hsb
    rw [hvc d hd, map_smul, colShift_eq]
    exact om_model S (defPair_top t (lastIx D)) (inRange_top t (lastIx D)) he (Tc (lastIx D)) (hTc (lastIx D)) _ cc
      (lat_col S ht k hk) hcc _ hsb
  have hsr : ∀ d ∈ τ.support, rowShift S k (S.Z.vec (d.2 (lastIx D))) =
      Tr (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) := by
    intro d hd
    have hsb := sb_std S ht (defPair_chi (lastIx D)) (d.2 (lastIx D)) ((hdat d hd).2 (lastIx D)).1
    rw [((hdat d hd).2 (lastIx D)).2.1] at hsb
    rw [hvr d hd, map_smul, rowShift_eq]
    exact om_model S (defPair_chi (lastIx D)) (inRange_chi (lastIx D)) he (Tr (lastIx D)) (hTr (lastIx D)) _ cr
      (lat_row S ht k hk) hcr _ hsb
  have key := GlobalTheory.funProd_multilinear_sum_eq (prodForm Tc Tr w v) τ
    (fun d j => ⟨Function.update (fun j => (d.1 j).fn) (lastIx D)
      (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j, Submodule.mem_top⟩)
    (fun d j => ⟨(d.1 j).fn, Submodule.mem_top⟩)
    (fun d i => ⟨Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i,
      Submodule.mem_top⟩)
    (fun d i => ⟨(d.2 i).fn, Submodule.mem_top⟩) hloc
  simp only [prodForm_apply] at key
  rw [Finsupp.sum, Finsupp.sum] at key ⊢
  refine (Finset.sum_congr rfl fun d hd => ?_).trans (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [mul_assoc]
    congr 2
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [show (fun j => S.Z.vec (d.1 j)) = fun j => Tc j (d.1 j).fn from funext (hvc d hd), hsc d hd,
        ← Function.apply_update (fun j => ⇑(Tc j)) (fun j => (d.1 j).fn) (lastIx D)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [show (fun i => S.Z.vec (d.2 i)) = fun i => Tr i (d.2 i).fn from funext (hvr d hd), hsr d hd,
        ← Function.apply_update (fun i => ⇑(Tr i)) (fun i => (d.2 i).fn) (lastIx D)]
  · rw [mul_assoc]
    congr 2
    · exact Finset.prod_congr rfl fun j _ => by rw [hvc d hd]
    · exact Finset.prod_congr rfl fun i _ => by rw [hvr d hd]

end GlobalTheory.LastVertexTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansion
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm


set_option maxHeartbeats 1000000 in
theorem columnInduction : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ (I : locPl ch.G t → Type) (S : ∀ w, Finset (I w)) (x : ∀ w, I w → ℂ) (d : ∀ w, I w → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : ∀ w, I w → Combs ch.G), (∀ w, ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).e = eL w ∧ IsCombOf ch.W (d w i j) ((c w i).1 j)) → (∀ w (y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))), (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0) → ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ) (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).e = e ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧ (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (u j)) → ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 u) 0) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u : ColPt ch.G, evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) 1 u 0 = (∏ w, ζ w) * ∑ a ∈ SJ, xJ a * evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    (((_root_.GlobalTheory.PlaceChain.points.and GlobalTheory.T.subset_place_vectors_and_steps).and (_root_.GlobalTheory.FockPlace.main.and _root_.GlobalTheory.LocAsm.exists_comb_op)).and ((_root_.GlobalTheory.ColComb.main.and _root_.GlobalTheory.ProdDatum.prod_datum).and (_root_.GlobalTheory.ColAtPart.colAt_smul_of_mul_idem.and _root_.GlobalTheory.VacComb.main)))
  obtain ⟨⟨⟨hA, hB⟩, hC, hD⟩, ⟨hE, hF⟩, hG, hZ⟩ := h
  intro s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd hfd eL heL I S x d c hdc hexp
  obtain ⟨he_sum, hsub, hmul⟩ := _root_.GlobalTheory.IdemSingleSum.sum_single D e (locPl ch.G t) he eL heL
  obtain ⟨V, hV0, hVu, hVth, hVst⟩ := hB t e he φ hφ fd hfd eL heL
  have hpts := fun (p : Pts ch.G) (hp : IsRealPt p) => hA s t β b b₀ hb hb₀ eL heL p hp
  choose q hq0 hqu hqst using hpts
  choose Tc hTc using hD
  obtain ⟨fl, hfl⟩ : ∃ fl : locPl ch.G t → (∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) → ℂ,
      ∀ w y, fl w y = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1)
        (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w))
          ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hexp' : ∀ w y, (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = fl w y :=
    fun w y hy => (hexp w y hy).trans (hfl w y).symm
  have hflG : ∀ (w' : locPl ch.G t) (e' : AE D), e' * eL w' = eL w' → ∀ u, fl w' (fun j => e' • u j) = fl w' u := by
    intro w' e' he' u
    rw [hfl, hfl, hG t w' (eL w') e' (heL w') he' u]

  have hcomb1 : ∀ (S' T' : HSp D) (f : WO S' T' → ℂ), comb ch.W.ψ S' T' (Finsupp.single 0 1) f = f := by
    intro S' T' f
    rw [GlobalTheory.DisjComb.comb_single]
    funext y
    simp [heisO, symplOH, symplO, hO]
  have hcombC1 : ∀ C : BiFam ch.G, combC ch.W ((fun _ => Finsupp.single 0 1), 0) C = C := by
    intro C
    funext j y z
    simp only [combC, biComb, hcomb1]

  have hidem : ∀ (S' : Finset (locPl ch.G t)), (∑ w ∈ S', eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S', eL w := by
    intro S'
    rw [hmul, Finset.inter_self]
  have hidem1 : ∀ w : locPl ch.G t, eL w * eL w = eL w := by
    intro w
    have h := hmul {w} {w}
    rw [Finset.inter_self, Finset.sum_singleton] at h
    exact h
  have hsubmul : ∀ (S' : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∈ S' → (∑ w ∈ S', eL w) * eL w = eL w := by
    intro S' w hw
    have h := hmul S' {w}
    rw [Finset.inter_singleton_of_mem hw, Finset.sum_singleton] at h
    exact h
  have hhalf : ∀ (a : AE D), a * a = a → ∀ {m n : ℕ} (y : Mx D m n), IsHalf a (a • y) := by
    intro a ha m n y i j
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ha]
  have key : ∀ S' : Finset (locPl ch.G t), ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ)
      (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j))
      (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ),
      (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).P = S'.map (Function.Embedding.subtype _) ∧
        (dJ a j).e = ∑ w ∈ S', eL w ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧
      (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf (∑ w ∈ S', eL w) (u j)) →
        ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w ∈ S', fl w u) ∧
      ∀ (P : PolDown ch.G) (p : Pts ch.G) (hp : IsRealPt p) (u : ColPt ch.G),
        evT (conAt ch.W hM (fockD ch.W t (V S') P) (q p hp S')) 1 u 0 = (∏ w ∈ S', ζ w) * ∑ a ∈ SJ, xJ a *
          evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      refine ⟨Unit, {()}, fun _ => 1, fun _ j => FinDatum.vacuum ch.G t (.top t j), fun _ _ => Finsupp.single 0 1, ?_, ?_, ?_⟩
      · intro a _ j
        refine ⟨?_, ?_, hZ t j⟩
        · rw [Finset.map_empty]; rfl
        · rw [Finset.sum_empty]; rfl
      · intro u hu
        have h0 : ∀ j, u j = 0 := by
          intro j
          ext a b'
          have := hu j a b'
          rw [Finset.sum_empty, zero_mul] at this
          exact this.symm
        simp only [Finset.sum_singleton, Finset.prod_empty, one_mul]
        refine Finset.prod_eq_one fun j _ => ?_
        rw [h0 j]
        show halfInd (0 : AE D) _ 0 = 1
        unfold halfInd
        rw [if_pos ⟨zero_mem _, fun a b' => by simp⟩]
      · intro P p hp u
        simp only [hV0, hq0 p hp, Finset.prod_empty, Finset.sum_singleton, one_mul, hcombC1]
    | insert w S₀ hw ih =>
      obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := ih
      have hPw : ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).P = {w.1} := by
        intro i hi j
        have h := (d w i j).e_is
        rw [(hdc w i hi j).1] at h
        exact _root_.GlobalTheory.IdemSumSet.places_eq_of_isIdemSum D _ _ _ h (heL w)
      have hsum : ∑ w' ∈ insert w S₀, eL w' = eL w + ∑ w' ∈ S₀, eL w' := Finset.sum_insert hw
      have hmap : (insert w S₀).map (Function.Embedding.subtype (· ∈ locPl ch.G t)) =
          {w.1} ∪ S₀.map (Function.Embedding.subtype (· ∈ locPl ch.G t)) := by
        rw [Finset.map_insert, Finset.insert_eq]; rfl
      have hs : IsIdemSum (eL w + ∑ w' ∈ S₀, eL w') ({w.1} ∪ S₀.map (Function.Embedding.subtype _)) := by
        have := hsub (insert w S₀)
        rwa [hsum, hmap] at this
      have hF' : ∀ (k : I w × J) (j : Fin D.R.m),
          ∃ (dd : FinDatum ch.G t (.top t j)) (cc : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), k.1 ∈ S w → k.2 ∈ SJ →
            dd.P = (d w k.1 j).P ∪ (dJ k.2 j).P ∧ dd.e = (d w k.1 j).e + (dJ k.2 j).e ∧ IsCombOf ch.W dd cc ∧
            (∀ y, IsHalf dd.e y → dd.fn y = (d w k.1 j).fn ((d w k.1 j).e • y) * (dJ k.2 j).fn ((dJ k.2 j).e • y)) ∧
            ∀ f, comb ch.W.ψ _ _ cc f = comb ch.W.ψ _ _ ((c w k.1).1 j) (comb ch.W.ψ _ _ (cJ k.2 j) f) := by
        intro k j
        by_cases hk : k.1 ∈ S w ∧ k.2 ∈ SJ
        · have hId : IsIdemSum ((d w k.1 j).e + (dJ k.2 j).e) ((d w k.1 j).P ∪ (dJ k.2 j).P) := by
            rw [(hdc w k.1 hk.1 j).1, (h1 k.2 hk.2 j).2.1, hPw k.1 hk.1 j, (h1 k.2 hk.2 j).1]
            exact hs
          obtain ⟨dd, cc, hh⟩ := hF t j (d w k.1 j) (dJ k.2 j) ((c w k.1).1 j) (cJ k.2 j) hId
            (hdc w k.1 hk.1 j).2 (h1 k.2 hk.2 j).2.2
          exact ⟨dd, cc, fun _ _ => hh⟩
        · exact ⟨FinDatum.vacuum ch.G t (.top t j), 0, fun h1' h2' => absurd ⟨h1', h2'⟩ hk⟩
      choose dF cF hdF using hF'
      refine ⟨I w × J, S w ×ˢ SJ, fun k => x w k.1 * xJ k.2, dF,
        fun k j => if h : j < D.R.m then cF k ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
      · intro k hk j
        obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
        obtain ⟨hP, he', hc, -, -⟩ := hdF k j hk1 hk2
        refine ⟨?_, ?_, ?_⟩
        · rw [hP, hPw k.1 hk1 j, (h1 k.2 hk2 j).1, hmap]
        · rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1, hsum]
        · dsimp only
          rw [dite_eq_left j.2]
          exact hc
      · intro u hu
        have hu' : ∀ j, IsHalf (eL w + ∑ w' ∈ S₀, eL w') (u j) := fun j => by rw [← hsum]; exact hu j
        have hfn : ∀ k ∈ S w ×ˢ SJ, ∀ j, (dF k j).fn (u j) =
            (d w k.1 j).fn (eL w • u j) * (dJ k.2 j).fn ((∑ w' ∈ S₀, eL w') • u j) := by
          intro k hk j
          obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
          obtain ⟨-, he', -, hfn', -⟩ := hdF k j hk1 hk2
          rw [hfn' (u j) (by rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1]; exact hu' j), (hdc w k.1 hk1 j).1,
            (h1 k.2 hk2 j).2.1]
        have hA' : ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (eL w • u j) = fl w u :=
          (hexp' w _ fun j => hhalf _ (hidem1 w) (u j)).trans (hflG w (eL w) (hidem1 w) u)
        have hB' : ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn ((∑ w' ∈ S₀, eL w') • u j) = ∏ w' ∈ S₀, fl w' u :=
          (h2 _ fun j => hhalf _ (hidem S₀) (u j)).trans
            (Finset.prod_congr rfl fun w' hw' => hflG w' _ (hsubmul S₀ w' hw') u)
        rw [Finset.sum_congr rfl fun k hk => by rw [Finset.prod_congr rfl fun j _ => hfn k hk j],
          Finset.sum_product, Finset.prod_insert hw, ← hA', ← hB', Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
      · intro P p hp u
        obtain ⟨r, r₀, h, hr, hr₀, htl, hhr, hhr₀⟩ := hqst p hp S₀ w hw
        have hloc := fun j => hC t (eL w) (V S₀) (V (insert w S₀)) P j _ (hVth S₀ j) (hVst S₀ w hw j)
        have hPC := hζ w (eL w) (heL w) M hM r r₀ h hr hr₀ htl (GlobalTheory.LocAsm.exOne (φ w)) (fun _ _ _ => rfl)
          (fockD ch.W t (V S₀) P) (fockD ch.W t (V (insert w S₀)) P) (fun j => (hloc j).1) (fun j => (hloc j).2)
          (I w) (S w) (x w) (d w) (c w) (hdc w) (hexp w) u
        rw [← hhr, hPC, hhr₀]
        have hIH : (fun u => evT (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀)) 1 u 0) =
            (∏ w' ∈ S₀, ζ w') • ∑ a ∈ SJ, xJ a • (fun u => evT (combC ch.W (cJ a, 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0) := by
          funext u'
          rw [h3 P p hp u']
          simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
        have hstep : ∀ i ∈ S w, evT (combC ch.W (c w i) (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀))) 1 u 0 =
            (∏ w' ∈ S₀, ζ w') * ∑ a ∈ SJ, xJ a * evT (combC ch.W ((fun j => if h : j < D.R.m then cF (i, a) ⟨j, h⟩ else 0), 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
          intro i hi
          set_option synthInstance.maxHeartbeats 100000 in
            rw [congrFun (hTc (c w i) _) u, hIH, map_smul, map_sum]
          simp only [map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun a ha => ?_
          congr 1
          rw [← congrFun (hTc (c w i) _) u]
          refine hE (c w i) (cJ a) _ ?_ _ u
          intro j hj f
          rw [dite_eq_left hj]
          exact (hdF (i, a) ⟨j, hj⟩ hi ha).2.2.2.2 f
        rw [Finset.prod_insert hw, Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hstep i hi]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
  obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := key Finset.univ
  refine ⟨J, SJ, xJ, dJ, cJ, fun a ha j => ⟨(h1 a ha j).2.1.trans he_sum.symm, (h1 a ha j).2.2⟩, fun u hu => ?_,
    fun P p hp u => ?_⟩
  · rw [h2 u (fun j => by rw [← he_sum]; exact hu j)]
    exact Finset.prod_congr rfl fun w _ => hfl w u
  · have := h3 P p hp u
    rwa [hVu, hqu p hp] at this

end GlobalTheory.LocAsm

end
end

