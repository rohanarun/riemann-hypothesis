module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0047
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntegrableAndBoundedLinearForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitOnto

variable {D : D7}

theorem eq_zero_at_off (P : Pl D → Prop) {a : AE D} (h1 : a ∈ idAt D P) (h2 : a ∈ idOff D P) : a = 0 := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (_root_.GlobalTheory.FinPl.localComponents D P).1
  rw [← (hA a).1 h1]
  exact (hO a).1 h2

theorem mulVec_off {S : HSp D} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) {y : Fin S.rank → AE D}
    (hy : ∀ i, y i ∈ idAt D P) : mt S b *ᵥ y = y := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  have key : (mt S b - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    apply eq_zero_at_off P
    · exact Ideal.mul_mem_left _ _ (hy j)
    · exact Ideal.mul_mem_right _ _ (by simpa using hb i j)
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem moves_off {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : GA D S} (hb : b ∈ grpOff S P) :
    Moves S b L L P := by
  intro y hy
  rw [mulVec_off hb hy]

theorem moves_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} : Moves S 1 L L P := by
  intro y _
  rw [PlacesAdeles.mt_one, Matrix.one_mulVec]

theorem moves_list_prod {S : HSp D} {L : Lat S} {P : Pl D → Prop} :
    ∀ l : List (GA D S), (∀ a ∈ l, Moves S a L L P) → Moves S l.prod L L P
  | [], _ => by rw [List.prod_nil]; exact moves_one
  | a :: l, h => by
    rw [List.prod_cons]
    exact PlacesAdeles.moves_mul (h a List.mem_cons_self) (moves_list_prod l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem prod_ofFn_single {M : Type*} [Monoid M] :
    ∀ {r : ℕ} (f : Fin r → M) (i : Fin r), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | r + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · have hprod : (List.ofFn (fun j : Fin r => f j.succ)).prod = 1 := by
        apply List.prod_eq_one
        rw [List.forall_mem_ofFn_iff]
        exact fun j => h j.succ (Fin.succ_ne_zero j)
      rw [hprod, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact prod_ofFn_single (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

def locHom (S : HSp D) {k : Type} [Ring k] (f : AE D →+* k) : GA D S →* Matrix (Fin S.rank) (Fin S.rank) k where
  toFun a := (mt S a).map f
  map_one' := by rw [PlacesAdeles.mt_one]; exact Matrix.map_one f f.map_zero f.map_one
  map_mul' a b := by rw [PlacesAdeles.mt_mul]; exact Matrix.map_mul

section Place

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_off (q : SplitPt D k) {a : AE D} (ha : a ∈ idOff D (· = q.v)) : q.pr a = 0 := by
  have h1 : q.e * a = 0 := eq_zero_at_off (· = q.v)
    (Ideal.mul_mem_right a _ (FrameLat.e_mem_idAt (p := q))) (Ideal.mul_mem_left _ q.e ha)
  have h2 : q.pr q.e = 1 := by rw [← FrameLat.sec_one (p := q), q.pr_sec]
  calc q.pr a = q.pr q.e * q.pr a := by rw [h2, one_mul]
    _ = 0 := by rw [← map_mul, h1, map_zero]

theorem map_off (q : SplitPt D k) {S : HSp D} {b : GA D S} (hb : b ∈ grpOff S (· = q.v)) :
    (mt S b).map q.pr = 1 := by
  rw [grpOff, PlacesAdeles.mem_congGrp] at hb
  ext i j
  have h := pr_off q (hb i j)
  rw [map_sub, sub_eq_zero] at h
  rw [Matrix.map_apply, h, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem one_place (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) (q : SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) (hI : IntIn q S F N) (x : GL Y k) (hx : x ∈ GlobalTheory.SplitWeil.KO k Y) :
    ∃ g, InK S N (· = q.v) g ∧ (mt S g).map q.pr = F.β * x.val * F.γ := by
  classical
  have H := (GlobalTheory.LocGrp.local_groups D k (GlobalTheory.LocMod.Place.ofSplitPt q)).1 S Y F
  choose glf hglf using fun gk => (H.1 gk).exists
  let gl : GL Y k →* GA D S := MonoidHom.mk' glf fun a b =>
    (H.1 (a * b)).unique (hglf (a * b)) (H.2.2 _ _ _ _ (hglf a) (hglf b))
  let β : GlobalTheory.FinPl.Frame q S Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun g => (hglf g).1, fun g => (hglf g).2⟩
  obtain ⟨Λ, -, hΛ, hK⟩ := GlobalTheory.FinPl.FrameLat.exists_lat D k q S Y β N hN
  have hmem : ∀ y : Y → k, y ∈ Λ ↔ ∀ j, y j ∈ 𝒪[k] := fun y => (hΛ y).trans (hI y).symm
  obtain ⟨x₀, rfl⟩ := hx
  have hint : ∀ (z : GL Y 𝒪[k]) (y : Y → k), (∀ j, y j ∈ 𝒪[k]) →
      ∀ j, (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z • y) j ∈ 𝒪[k] := by
    intro z y hy j
    change ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) z).val *ᵥ y) j ∈ 𝒪[k]
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun l _ => mul_mem (z.val j l).2 (hy l)
  have hstab : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x₀ • Λ = Λ := by
    ext y
    rw [GlobalTheory.LatPair.mem_smul_iff, hmem, hmem]
    constructor
    · intro h
      have := hint x₀ _ h
      rwa [smul_inv_smul] at this
    · intro h
      rw [← map_inv]
      exact hint x₀⁻¹ y h
  exact ⟨β.gl _, (hK _).2 hstab, (hglf _).2⟩

end Place

theorem exists_of_local : ∀ {D : D7} (S : HSp D) (N : Lat S), IsSelfDualC S N → ∀ {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i)), Function.Injective (fun i => (q i).v) → (∀ i, IntIn (q i) S (F i) N) → ∀ x : (i : Fin r) → GL (Y i) (k i), (∀ i, x i ∈ GlobalTheory.SplitWeil.KO (k i) (Y i)) → ∃ g, InK S N (fun p => ∃ i, (q i).v = p) g ∧ ∀ i, (mt S g).map (q i).pr = (F i).β * (x i).val * (F i).γ := by
  intro D S N hN r k _ _ _ _ q Y _ _ F hinj hI x hx
  classical
  choose g hgK hgm using fun i => one_place S N hN (q i) (F i) (hI i) (x i) (hx i)
  have hgrp : ∀ i, g i ∈ grpAt S (· = (q i).v) := fun i => (hgK i).1
  have hoff : ∀ i j, j ≠ i → g j ∈ grpOff S (· = (q i).v) := fun i j hji =>
    PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_le_idOff (fun e => hji (hinj e).symm)) (hgrp j)
  refine ⟨(List.ofFn g).prod, ⟨?_, ?_⟩, ?_⟩
  · refine _root_.list_prod_mem fun a ha => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
    exact PlacesAdeles.congGrp_mono (PlacesAdeles.idAt_single_le ⟨j, rfl⟩) (hgrp j)
  · have hlat := ((_root_.GlobalTheory.FinPl.localComponents D (fun p => ∃ i, (q i).v = p)).2 S).2.2.2 N
    have hloc : ∀ i, Moves S (List.ofFn g).prod N N (· = (q i).v) := fun i =>
      moves_list_prod _ fun a ha => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 ha
        by_cases hji : j = i
        · subst hji; exact (hgK j).2
        · exact moves_off (hoff i j hji)
    intro y hy
    rw [hlat y hN.1, hlat _ hN.1]
    have hy' := PlacesAdeles.supp_mulVec S _ (List.ofFn g).prod hy
    have hey : ∀ v e, e ∈ intAt D (· = v) → ∀ i, (e • y) i ∈ idAt D (· = v) := fun v e he i => by
      simpa [smul_eq_mul] using Ideal.mul_mem_right (y i) _ he.1
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨hy', fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      rw [← Matrix.mulVec_smul]
      exact (hloc i _ (hey _ e he)).1 (h2 _ ⟨i, rfl⟩ e he)
    · rintro ⟨-, h2⟩
      refine ⟨hy, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := hv
      have := h2 _ ⟨i, rfl⟩ e he
      rw [← Matrix.mulVec_smul] at this
      exact (hloc i _ (hey _ e he)).2 this
  · intro i
    change locHom S (q i).pr (List.ofFn g).prod = _
    rw [map_list_prod, List.map_ofFn, prod_ofFn_single _ i]
    · exact hgm i
    · intro j hji
      exact map_off (q i) (hoff i j hji)

end GlobalTheory.SplitOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointWeilCharConductorOneOfUnits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.SplitWeilChar

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (q : SplitPt D k) (hU : q.UnitAA) : q.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := GlobalTheory.SplitCharCond.exists_idem q
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = q.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := GlobalTheory.SplitCharCond.pr_int q (hU.1 _ hm).2.2
  rwa [map_mul, GlobalTheory.SplitCharCond.pr_pair_tmul q h, map_one, map_one, mul_one] at this

theorem valuation_pr_incA_xi0_eq_one_of_unitAA (q : SplitPt D k) (hU : q.UnitAA) : valuation k (q.pr (incA D D.host.xi0)) = 1 := by
  have h1 := (Valuation.mem_integer_iff _ _).1 (GlobalTheory.SplitCharCond.xi_zero_projection_integral q hU)
  have h2 := (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hm : q.pr (incA D D.host.xi0) * q.pr (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  have h3 := congrArg (valuation k) hm
  rw [map_mul, map_one] at h3
  by_contra hne
  have hlt : valuation k (q.pr (incA D D.host.xi0)) < 1 := lt_of_le_of_ne h1 hne
  have : valuation k (q.pr (incA D D.host.xi0)) * valuation k (q.pr (incA D D.host.xi0⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

end GlobalTheory.SplitWeilChar

namespace GlobalTheory.SplitWeilChar

theorem weil_char_conductor_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → q.UnitAA → ∃ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk ∧ HasConductor ψk 1 := by
  intro D k _ _ _ _ q ψ hψ hU
  obtain ⟨⟨ψk, hk⟩, -⟩ := GlobalTheory.LocChar.weil_char_split D k (ofSplit q) ψ hψ
  set u : k := q.pr (incA D D.host.xi0) with hu
  have hv : valuation k u = 1 := valuation_pr_incA_xi0_eq_one_of_unitAA q hU
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hv; exact zero_ne_one hv
  let χ : AddChar k Circle := ψk.mulShift u⁻¹
  have hχ : q.IsChar ψ χ := by
    intro a
    have e1 : (χ a : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec (u⁻¹ * a)) := hk (u⁻¹ * a)
    have e2 := GlobalTheory.SplitCharCond.sec_mul_pr q (u⁻¹ * a) (incA D D.host.xi0)
    rw [← hu, show u⁻¹ * a * u = a by field_simp] at e2
    rw [e1, ← e2]
  have hc1 : HasConductor χ 1 := GlobalTheory.SplitCharCond.hasConductor_one D k q ψ χ hψ hχ hU
  have hcu : HasConductor χ (Units.mk0 u hu0) := by
    intro x
    rw [Units.val_mk0, hv]
    have := hc1 x
    rwa [Units.val_one, map_one] at this
  have he : ψk = χ.mulShift ((Units.mk0 u hu0 : kˣ) : k) := by
    ext x
    simp only [χ, AddChar.mulShift_apply, Units.val_mk0]
    rw [← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
  refine ⟨ψk, hk, ?_⟩
  rw [he]
  exact GlobalTheory.CollapseCompare.hasConductor_mulShift hcu

end GlobalTheory.SplitWeilChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataConductorOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SymChainAt
open GlobalTheory.FinPl (SplitPt idAt intAt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem pr_e : q.pr q.e = 1 := by rw [← sec_one, q.pr_sec]

theorem pr_e_mul (x : AE D) : q.pr (q.e * x) = q.pr x := by rw [map_mul, pr_e, one_mul]

theorem place_facts {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) :
    (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  obtain ⟨k₀, _, _, _, _, q₀, he, -, hi, hd⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP q.e h
  refine ⟨fun a => ?_, ?_⟩
  · rw [← hi, q.int_iff, q₀.int_iff]
    change finPart D (q.sec (q.pr _)) ∈ _ ↔ finPart D (q₀.sec (q₀.pr _)) ∈ _
    rw [q.sec_pr, q₀.sec_pr, he]
  · have hs : Function.Surjective (fun x => q.pr (q₀.sec x)) := fun y =>
      ⟨q₀.pr (q.sec y), by simp only [q₀.sec_pr, he, pr_e_mul, q.pr_sec]⟩
    have := hs.denseRange.comp hd (q.cont_pr.comp q₀.cont_sec)
    convert this using 1
    funext a
    change q.pr _ = q.pr (q₀.sec (q₀.pr _))
    rw [q₀.sec_pr, he, pr_e_mul]

def prO : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem sec_mul (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idl_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul q x y
  rw [h, sec_one] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idl (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idl_mul q _ _ x.mul_inv, idl_mul q _ _ x.inv_mul⟩

end Place

end GlobalTheory.LocMod.SymChainAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
section
namespace I195MixedCoordinates_e532927a36ed71d9eb873635

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_e532927a36ed71d9eb873635

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section
namespace GlobalTheory.Unf

theorem flatFun_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vU : VolU D ρ) (x : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x.transpose → ∀ Φ, IsThetaFunO ψ V W Φ → ∀ K : Set (GA D V × GA D W), IsCompact K → ∃ M : UX D ρ → ℝ, Integrable M vU.ν ∧ ∀ p ∈ K, ∀ y w u, ‖flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (rat x) y (om p Φ) w u‖ ≤ M u := by
  intro D ψ V V₀ W W₀ ρ σ dV dW vS vT χV χW om hW vU x hx Φ hΦ K hK
  have hn : ∀ a, ‖ψ a‖ = 1 := hW.std.1.2.1
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨K', hK', hC⟩ := _root_.GlobalTheory.Unf.mixS_om_compact_maj D ψ V W χV χW om hW θ hθ V₀ ρ dV vS Φ hΦ K hK
  obtain ⟨N, hN⟩ := _root_.GlobalTheory.Unf.pull_integrable D θ hθ W.rank ρ vU x hx
  obtain ⟨C, hC⟩ := hC N
  refine ⟨fun u => C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1), (hN K' hK').const_mul C, ?_⟩
  intro p hp y w u
  have hT := vT.covol
  unfold flatFun evalAt
  rw [norm_mul, norm_star]
  have h1 : ‖psiUni ψ u.1‖ = 1 := hn _
  rw [h1, one_mul]
  unfold _root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.target
  have hb : ∀ ξ ∈ vT.𝓕, ‖heisO ψ V₀ W (dW.incX V₀ ξ) (heisO ψ V₀ W (dW.incAdj V₀ y) (heisO ψ V₀ W (dW.inc0 V₀ w)
      ((_root_.I195MixedCoordinates_14b5fd3aa93c7f4842f1a892.source dV) W ψ vS.μ vS.𝓕 (om p Φ) ((rat x : Mx D W.rank ρ) ⬝ u.1.1)))) 0‖ ≤ C * maj θ K' N ((rat x : Mx D W.rank ρ) ⬝ u.1.1) := by
    intro ξ _
    rw [dW.integrandT_eq, norm_mul, hn, one_mul]
    exact hC p hp _ _
  have := norm_setIntegral_le_of_norm_le_const (by rw [hT.2.2]; exact ENNReal.one_lt_top) hb
  rw [measureReal_def, hT.2.2, ENNReal.toReal_one, mul_one] at this
  exact this
end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.Flat

variable {D : D7}

def coreMap {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) : WO V₀ W₀ →+ WO V W :=
  (dV.ext0 W).comp (dW.inc0 V₀)

theorem coreMap_eq {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) :
    ⇑(coreMap dV dW) = fun w => (dW.j0 * w) * dV.p0 := by
  funext w; rfl

theorem continuous_coreMap {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) :
    Continuous (coreMap dV dW) := by
  rw [coreMap_eq]
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem coreMap_finPart {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (w : WO V₀ W₀)
    (h : w.map (finPart D) = 0) : (coreMap dV dW w).map (finPart D) = 0 := by
  show ((dW.j0 * w) * dV.p0).map (finPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem coreMap_infPart {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (w : WO V₀ W₀)
    (h : w.map (infPart D) = 0) : (coreMap dV dW w).map (infPart D) = 0 := by
  show ((dW.j0 * w) * dV.p0).map (infPart D) = 0
  rw [Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul]

theorem flatLaw : ∀ D : D7, FlatLaw D := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y Ψ hΨ
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hF := _root_.GlobalTheory.Unf.FlatForm.flatAt_isSobForm D ψ hψ θ hθ V V₀ W W₀ ρ σ dV dW vS vT vU x hx y
  refine ⟨hF.1 Ψ hΨ, ?_⟩
  exact _root_.GlobalTheory.ThetaMap.thetaMap D ψ hψ θ hθ V W V₀ W₀ (coreMap dV dW) (continuous_coreMap dV dW)
    (coreMap_finPart dV dW) (coreMap_infPart dV dW)
    (fun f => flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν (rat x) y f) (hF.2 0)
    (fun f w hf => ((_root_.GlobalTheory.FlatHeis.flatAt_heisO D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU (rat x) y f hf).2.1 w))
    (fun f γ hf => ((_root_.GlobalTheory.FlatHeis.flatAt_heisO D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU (rat x) y f hf).2.2 γ)) Ψ hΨ

end GlobalTheory.Unf.Flat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSumDisjointUnion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod GlobalTheory.Mem GlobalTheory.Mem.Col2 Formalism.L2.Col Formalism.L2.Forms
open scoped Classical

namespace GlobalTheory.IdemSumAdd

theorem idemSum_union : ∀ (D : D7) (a b : AE D) (P Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), Disjoint P Q → (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → IsIdemSum a P → IsIdemSum b (P ∪ Q) → b = a + ∑ PP ∈ Q, es PP := by
  intro D a b P Q es hPQ hQ ha hb
  rw [← GlobalTheory.ExportSeries.idem_eq ha, ← GlobalTheory.ExportSeries.idem_eq hb, GlobalTheory.ExportSeries.idem,
    GlobalTheory.ExportSeries.idem, Finset.sum_union hPQ]
  congr 1
  exact Finset.sum_congr rfl fun PP hPP => GlobalTheory.ExportSeries.idemAt_eq (hQ PP hPP)

end GlobalTheory.IdemSumAdd
end

