module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2460
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ZarhinGeometricOfSemistableReduction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2456
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordTermTranslateNormalisedGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumTerm

variable {X Y Z : Scheme.{0}}

theorem scal_spec {A B : Type} [CommRing A] [CommRing B] (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ Spec.map (CommRingCat.ofHom φ)) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem gs_scal {A : Type} [CommRing A] (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem exists_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) : ∃ t : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval t r z J = gs r z ⊤ a * sval s r z J := by
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE le_top).op).hom a * s.f i, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, s.compat i j, mul_left_comm]
    congr 2
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · have hm := hJ.mem φ r
    exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem exists_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  intro R _ _ _ D a h h' N s₀ ν u₀ hu₀ ρ H
  obtain ⟨p, hp⟩ := exists_sec D.toPre.P.isLB (φ' := tφ D.toPre a (shift h h' N (-1) ν)) (ε' := tε N (-1))
    (fun U _ g => by
      simp only [Fintype.prod_sum_type, dε, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec s₀ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left u₀ hu₀)
  obtain ⟨t, ht⟩ := exists_smul (scal D.toPre.P.A.hom ρ) p
  refine ⟨t, fun u hu Z x z J hJ => ?_, fun e he Z x z J hJ => ?_⟩
  · have e₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left =
        (DegPre.trF D.toPre (FractionRing R) ν).left ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      simp only [DegPre.trF, padd, lift_snd]
      rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
    have e₂ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
        ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
          (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
      have j : jFK (R := R) (FractionRing R) = 𝟙 _ := by
        simp [jFK]
      rw [Over.w]
      refine (Over.w (fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_
      congr 1
      show jFK (R := R) (FractionRing R) ≫ jK R = jK R
      rw [j, Category.id_comp]
    rw [ht _ _ z J hJ, hp _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, H u hu Z x z J hJ, Category.assoc, e₁,
      scal_spec, gs_scal, gs_scal, Category.assoc, e₂, mul_left_comm]
  · rw [ht _ _ z J hJ, gs_scal, Category.assoc, pullback.condition, ← gs_scal, ← scal_spec,
      Ideal.Quotient.eq_zero_iff_mem.2 he]
    have : scal (pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (0 : R ⧸ maximalIdeal R ^ (e + 1)) = 0 := by
      simp only [scal, map_zero]
    exact (congrArg (· * _) ((congrArg (gs x z ⊤) this).trans (DVR.gs_zero x z ⊤ trivial))).trans (zero_mul _)

end GlobalTheory.MumTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormLeOfMemMapPow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CplDiv

theorem dvd_of_forall_mem_sup_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R), IsCpl j → ∀ (c s : R), (∀ e : ℕ, s ∈ Ideal.span {c} ⊔ (maximalIdeal O ^ e).map j) → c ∣ s := by
  intro O R _ _ _ _ j hj c s hs
  obtain ⟨e, he⟩ := hj
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal O) O) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion O (maximalIdeal O)
  haveI : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ e
  haveI : IsLocalRing R := e.isLocalRing
  have hjl : (maximalIdeal O).map j ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
      have := hu.map e.symm.toRingHom
      rw [← he a] at this
      simpa using this
    exact ha (isUnit_of_map_unit _ _ h1)
  have hJ : (maximalIdeal O).map j ≠ ⊤ := fun h => by
    have := hjl
    rw [h, top_le_iff] at this
    exact (maximalIdeal.isMaximal R).ne_top this
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ Ideal.span {c}) ((maximalIdeal O).map j) hJ
  have hmem : (Ideal.Quotient.mk (Ideal.span {c}) s : R ⧸ Ideal.span {c}) ∈ (⨅ i : ℕ, ((maximalIdeal O).map j) ^ i • ⊤ : Submodule R (R ⧸ Ideal.span {c})) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hs i)
    rw [Ideal.map_pow] at hv
    have : (Ideal.Quotient.mk (Ideal.span {c}) s : R ⧸ Ideal.span {c}) = v • (Ideal.Quotient.mk (Ideal.span {c}) 1) := by
      rw [← huv, Algebra.smul_def, map_one, _root_.mul_one, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hu, _root_.zero_add]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul hv trivial
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem

theorem exists_sub_mem_map_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R), IsCpl j → ∀ (s : R) (n : ℕ), ∃ t : O, s - j t ∈ (maximalIdeal O ^ n).map j := by
  intro O R _ _ _ _ j hj s n
  obtain ⟨e, he⟩ := hj
  have fg : (maximalIdeal O).FG := (maximalIdeal O).fg_of_isNoetherianRing
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ ((e.symm s).val n)
  refine ⟨t, ?_⟩
  have hker : e.symm s - algebraMap O _ t ∈ (AdicCompletion.eval (maximalIdeal O) O n).ker := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
    rw [Algebra.algebraMap_self, RingHom.id_apply, Submodule.mkQ_apply, ht, AdicCompletion.eval_apply, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map] at hker
  have h2 := Ideal.mem_map_of_mem e.toRingHom hker
  rw [Ideal.map_map] at h2
  have hc : e.toRingHom.comp (algebraMap O _) = j := RingHom.ext fun a => he a
  rw [hc] at h2
  simpa [he] using h2

theorem exists_norm_le_of_mem_map_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R) (p : ℕ) [Fact p.Prime] (ev : R →+* OO p) (n : ℕ) (t : R), t ∈ (maximalIdeal O ^ n).map j → ∃ g ∈ maximalIdeal O, ‖(ev t : PadicAlgCl p)‖ ≤ ‖(ev (j g) : PadicAlgCl p)‖ ^ n := by
  intro O R _ _ _ _ j p _ ev n t ht
  have hle1 : ∀ r : R, ‖(ev r : PadicAlgCl p)‖ ≤ 1 := fun r => (mem_OO_iff _).1 (ev r).2
  have hadd : ∀ (x y : R) (B : ℝ), ‖(ev x : PadicAlgCl p)‖ ≤ B → ‖(ev y : PadicAlgCl p)‖ ≤ B →
      ‖(ev (x + y) : PadicAlgCl p)‖ ≤ B := by
    intro x y B hx hy
    rw [map_add (f := _), AddMemClass.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  have hmul : ∀ (x y : R) (B : ℝ), ‖(ev y : PadicAlgCl p)‖ ≤ B → ‖(ev (x * y) : PadicAlgCl p)‖ ≤ B := by
    intro x y B hy
    rw [map_mul, MulMemClass.coe_mul, norm_mul]
    calc ‖(ev x : PadicAlgCl p)‖ * ‖(ev y : PadicAlgCl p)‖ ≤ 1 * ‖(ev y : PadicAlgCl p)‖ :=
          mul_le_mul_of_nonneg_right (hle1 x) (norm_nonneg _)
      _ ≤ B := by rw [_root_.one_mul]; exact hy
  obtain ⟨S, hS⟩ := (maximalIdeal O).fg_of_isNoetherianRing
  let N : O → ℝ := fun g => ‖(ev (j g) : PadicAlgCl p)‖
  obtain ⟨g, hgS, hgmax⟩ := (insert 0 S).exists_max_image N ⟨0, Finset.mem_insert_self _ _⟩
  have hgm : g ∈ maximalIdeal O := by
    rcases Finset.mem_insert.1 hgS with h | h
    · rw [h]; exact Ideal.zero_mem _
    · rw [← hS]; exact Ideal.subset_span h
  refine ⟨g, hgm, ?_⟩
  have c1 : ∀ a ∈ maximalIdeal O, N a ≤ N g := by
    intro a ha
    rw [← hS] at ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hgmax x (Finset.mem_insert_of_mem hx)
    | zero => exact hgmax 0 (Finset.mem_insert_self _ _)
    | add x y _ _ hx hy =>
      show ‖(ev (j (x + y)) : PadicAlgCl p)‖ ≤ N g
      rw [map_add (f := _)]; exact hadd _ _ _ hx hy
    | smul r x _ hx =>
      show ‖(ev (j (r • x)) : PadicAlgCl p)‖ ≤ N g
      rw [smul_eq_mul, map_mul]; exact hmul _ _ _ hx
  have c2 : ∀ k : ℕ, ∀ a ∈ maximalIdeal O ^ k, N a ≤ N g ^ k := by
    intro k
    induction k with
    | zero => intro a _; rw [pow_zero]; exact hle1 _
    | succ k ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro x hx y hy
        show ‖(ev (j (x * y)) : PadicAlgCl p)‖ ≤ N g ^ (k + 1)
        rw [map_mul, map_mul, MulMemClass.coe_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih x hx) (c1 y hy) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      · intro x y hx hy
        show ‖(ev (j (x + y)) : PadicAlgCl p)‖ ≤ N g ^ (k + 1)
        rw [map_add (f := _)]; exact hadd _ _ _ hx hy
  unfold Ideal.map at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact c2 n a ha
  | zero => rw [map_zero, ZeroMemClass.coe_zero, norm_zero]; exact pow_nonneg (norm_nonneg _) _
  | add x y _ _ hx hy => exact hadd _ _ _ hx hy
  | smul r x _ hx => rw [smul_eq_mul]; exact hmul _ _ _ hx

theorem val_stalkHom_eq : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (φ : M.Z.presheaf.stalk x →+* OO p), y (cPt p) = x → spMap φ ≫ M.Z.fromSpecStalk x = y → ∀ a : M.Z.presheaf.stalk x, M.val (gPt p ≫ y) (M.stalkHom x a) = ((φ a : OO p) : PadicAlgCl p) := by
  intro o' Ω _ _ _ M x p _ y φ hy hφ a
  have h : y (cPt p) ⤳ x := hy ▸ specializes_rfl
  have hψ : Spec.map (M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y) ≫ M.Z.fromSpecStalk x = y := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  haveI : Mono (M.Z.fromSpecStalk x) := inferInstance
  have heq : spMap φ = Spec.map (M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y) := by
    rw [← cancel_mono (M.Z.fromSpecStalk x), hφ, hψ]
  have hφψ := Spec.map_injective heq
  have e1 : M.stalkHom x a = (M.stalkEquiv x a : Ω) := rfl
  rw [e1, RatModel.val_gPt hy (M.stalkEquiv x a)]
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  have := congrArg (fun g => ((g.hom a : OO p) : PadicAlgCl p)) hφψ
  exact this.symm

theorem dvd_of_norm_le_at_classical : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (b : M.Z.presheaf.stalk x) (s : R), b ≠ 0 → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ‖(ev s : PadicAlgCl p)‖ ≤ ‖(ev (j b) : PadicAlgCl p)‖) → j b ∣ s := by
  intro o' Ω _ _ _ _ M hN U₀ hU₀ x hx R _ j hj b s hb hs
  haveI : IsNoetherianRing (M.O x) := GlobalTheory.FibreCorr.isNoetherianRing_O M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := isNoetherianRing_of_ringEquiv _ (M.stalkEquiv x).symm
  have hfO : M.stalkHom x b ∈ M.O x := (M.stalkEquiv x b).2
  have hf0 : M.stalkHom x b ≠ 0 := fun h => hb ((map_eq_zero_iff _ (M.stalkHom_injective x)).1 h)
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.Izumi.small_mod_principal o' Ω M hN U₀ hU₀ x hx _ hfO hf0
  refine dvd_of_forall_mem_sup_pow _ _ j hj (j b) s fun e => ?_
  obtain ⟨t, ht⟩ := exists_sub_mem_map_pow _ _ j hj s (max e (C e))
  obtain ⟨a, c, hac, hc⟩ := hC e (M.stalkEquiv x t) (by
    intro p _ y hy
    obtain ⟨V, _, _, _, ev₀, i, -, -, -, -, hev, -⟩ := GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hj p y hy.1
    have hsb := hs p y (i.comp ev₀) hy hev
    have hφ : spMap ((i.comp ev₀).comp j) ≫ M.Z.fromSpecStalk x = y := by
      rw [← hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hval := val_stalkHom_eq o' Ω M x p y _ hy.1 hφ
    have e1 : M.val (gPt p ≫ y) (M.stalkEquiv x t : Ω) = ((i.comp ev₀) (j t) : PadicAlgCl p) := hval t
    have e2 : M.val (gPt p ≫ y) (M.stalkHom x b) = ((i.comp ev₀) (j b) : PadicAlgCl p) := hval b
    obtain ⟨g, hg, hgn⟩ := exists_norm_le_of_mem_map_pow _ _ j p (i.comp ev₀) _ _ ht
    rw [e1, e2]
    have key : ((i.comp ev₀) (j t) : PadicAlgCl p) = ((i.comp ev₀) s : PadicAlgCl p) - ((i.comp ev₀) (s - j t) : PadicAlgCl p) := by
      simp
    have hmax : ‖((i.comp ev₀) s : PadicAlgCl p) - ((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ ≤ max ‖((i.comp ev₀) s : PadicAlgCl p)‖ ‖((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ := by
      rw [sub_eq_add_neg, ← norm_neg ((i.comp ev₀) (s - j t) : PadicAlgCl p)]
      exact IsUltrametricDist.norm_add_le_max _ _
    by_cases hle : ‖((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ ≤ ‖((i.comp ev₀) s : PadicAlgCl p)‖
    · left
      rw [key]
      exact hmax.trans ((max_le le_rfl hle).trans hsb)
    · right
      refine ⟨M.stalkHom x g, ⟨(M.stalkEquiv x g).2, ?_⟩, ?_⟩
      · have hnu : ¬ IsUnit (M.stalkEquiv x g) := fun h => hg (by simpa using h.map (M.stalkEquiv x).symm)
        rw [RatModel.isUnit_O_iff] at hnu
        by_cases h0 : (M.stalkEquiv x g : Ω) = 0
        · exact Or.inl h0
        · exact Or.inr fun h => hnu ⟨h0, h⟩
      · rw [hval g, key]
        have h1 : ‖((i.comp ev₀) (j g) : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 ((i.comp ev₀) (j g)).2
        have h2 := pow_le_pow_of_le_one (norm_nonneg _) h1 (le_max_right e (C e))
        exact hmax.trans ((max_le (le_of_not_ge hle) le_rfl).trans (hgn.trans h2)))
  have hmax : maximalIdeal (M.O x) = (maximalIdeal (M.Z.presheaf.stalk x)).map (M.stalkEquiv x) := by
    have : ((maximalIdeal (M.Z.presheaf.stalk x)).map (M.stalkEquiv x)).IsMaximal :=
      Ideal.map_isMaximal_of_equiv (M.stalkEquiv x)
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hspan : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := by
    have : {c : M.O x | ¬ IsUnit c} = (maximalIdeal (M.O x) : Set (M.O x)) := rfl
    rw [this, Ideal.span_eq]
  rw [hspan, hmax, ← Ideal.map_pow] at hc
  have hc' : (M.stalkEquiv x).symm c ∈ maximalIdeal (M.Z.presheaf.stalk x) ^ e := by
    obtain ⟨c₀, hc₀, hc₀e⟩ := (Ideal.mem_map_of_equiv (M.stalkEquiv x) c).1 hc
    rw [← hc₀e, RingEquiv.symm_apply_apply]
    exact hc₀
  have ht' : t = (M.stalkEquiv x).symm a * b + (M.stalkEquiv x).symm c := by
    apply (M.stalkEquiv x).injective
    apply Subtype.ext
    rw [map_add (f := _), map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hac
  have hle : (maximalIdeal (M.Z.presheaf.stalk x) ^ max e (C e)).map j ≤ (maximalIdeal (M.Z.presheaf.stalk x) ^ e).map j :=
    Ideal.map_mono (Ideal.pow_le_pow_right (le_max_left _ _))
  have hs' : s = (j t + (s - j t)) := by ring
  have hd := hle ht
  rw [hs']
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right hd)
  rw [ht', map_add (f := _), map_mul]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hc'))

end GlobalTheory.CplDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveToricMinorModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.SiegJoin

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isUnit_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {z : M.Z} {y : Ω}
    (hy : y ∈ X.O (f z)) (hu : IsUnit (⟨y, hf.map_mem_O hy⟩ : M.O z)) : IsUnit (⟨y, hy⟩ : X.O (f z)) := by
  obtain ⟨U, a, hz, rfl⟩ := hy
  rw [RatModel.isUnit_valF_iff hz]
  have hz' : z ∈ f ⁻¹ᵁ U := hz
  have e : (⟨valF X.pt U a, hf.map_mem_O ⟨U, a, hz, rfl⟩⟩ : M.O z) =
      ⟨valF M.pt (f ⁻¹ᵁ U) (f.app U a), RatModel.valF_mem_O hz' _⟩ :=
    Subtype.ext (hf.valF_app ⟨_, hz⟩ a).symm
  rw [e, RatModel.isUnit_valF_iff hz', ← Scheme.preimage_basicOpen] at hu
  exact hu

theorem div_iff_of_isHom {X M : RatModel o Ω} {f : M.Z ⟶ X.Z} (hf : X.IsHom M (AlgHom.id o Ω) f) {J : Type}
    {t : J → Ω} (hX : X.HasDiv t) (z : M.Z) (x : J) : M.Div t x z ↔ X.Div t x (f z) := by
  obtain ⟨i, hi⟩ := hX (f z)
  have hi' : M.Div t i z := hf.div hi
  refine ⟨fun hx => ?_, fun hx => hf.div hx⟩
  rw [hi.div_iff_isUnit]
  exact isUnit_of_isHom hf (hi.2 x) ((hi'.div_iff_isUnit x).1 hx)

end GlobalTheory.SiegJoin

namespace GlobalTheory.SiegJoin

theorem minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), S.Big → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (X M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE), MinorAt S X M U₀ EE f Xab ∧ IsOpen (abLocus Zh.G) ∧ (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
  intro o Ω _ _ _ _ S ρ hB hfin
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hT : S.HasTests := (_root_.GlobalTheory.ZH.hasTests_of_real _root_.GlobalTheory.SS.semistableReductionSt _root_.GlobalTheory.ZH.thmU_and_uTors.1 hL.1 hL.2 _root_.GlobalTheory.ZH.thmU_and_uTors.2 o Ω S ρ).1
  obtain ⟨n, a, GG, X, M, U₀, EE, f, Xab, hNm, hP, -, hO, hE, hH, hXab, hI, hgen, -⟩ := _root_.GlobalTheory.ZH.exists_minor_model o Ω S hT hfin
  obtain ⟨Zh⟩ := _root_.GlobalTheory.zhGeo_of_semistableReduction _root_.GlobalTheory.SS.semistableReductionSt o Ω S ρ hB M U₀ EE hO hE ⟨n, a, GG, hgen⟩
  have hsupI : ∀ z : M.Z, S.supI M z = S.supI X (f z) := fun z =>
    Set.ext fun x => div_iff_of_isHom hH hNm.1 z x
  have key : (abLocus Zh.G : Set M.Z) = f ⁻¹' (Xab : Set X.Z) := by
    rw [Zh.ab, hXab]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ThetaSys.TT, ThetaSys.HH, hsupI z]
  refine ⟨X, M, U₀, EE, f, Xab, Zh, ⟨hNm, hP, hNm.isNormalScheme, hO, hE, hH, hXab, hI⟩, ?_, key⟩
  rw [key]
  exact Xab.isOpen.preimage f.continuous

end GlobalTheory.SiegJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenFiniteOntoOfLevelCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_openAt_of_levAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (β : cycAway n →+* o) (S : ThetaSys o Ω) (u : Sp S.R ⟶ F.X) (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X)
    (f : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → X.IsHom M (AlgHom.id o Ω) f →
    IsIso (f ∣_ Xab) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → Set.range d ⊆ Xab →
    ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ f ⁻¹' Xab := by
  intro g n F o Ω _ _ _ β S u Y X M q f Xab d hL hf hiso hd hdo hrange
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [spMap, CommRingCat.ofHom_id, Spec.map_id]
  have hf' : M.pt ≫ f = X.pt := by simpa [RatModel.IsHom, hid] using hf
  have hd' : Y.pt ≫ d = X.pt := by simpa [RatModel.IsHom, hid] using hd
  set U : M.Z.Opens := f ⁻¹ᵁ d.opensRange with hUdef
  have hUle : U ≤ f ⁻¹ᵁ Xab := fun m hm => hrange hm
  have hopen : IsOpenImmersion (U.ι ≫ f) := by
    have e : U.ι ≫ f = M.Z.homOfLE hUle ≫ (f ∣_ Xab) ≫ Xab.ι := by
      rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
    rw [e]
    infer_instance
  have hrng : Set.range (U.ι ≫ f) = Set.range d := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact m.2
    · rintro ⟨y, rfl⟩
      have hy : d y ∈ Xab := hrange ⟨y, rfl⟩
      obtain ⟨m', hm'⟩ := (f ∣_ Xab).surjective ⟨d y, hy⟩
      have h1 : f ((f ⁻¹ᵁ Xab).ι m') = d y := by
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hm']
        rfl
      have h2 : (f ⁻¹ᵁ Xab).ι m' ∈ U := ⟨y, h1.symm⟩
      exact ⟨⟨_, h2⟩, h1⟩
  let e := IsOpenImmersion.isoOfRangeEq (U.ι ≫ f) d hrng
  have he : e.hom ≫ d = U.ι ≫ f := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨-, hfin, hsurj, hs, hpt⟩ := hL
  refine ⟨U, e.hom ≫ q, ⟨?_, inferInstance, inferInstance, ?_, ?_⟩, fun m hm => hUle hm⟩
  · obtain ⟨w⟩ : Nonempty (Sp Ω) := inferInstance
    refine ⟨M.pt w, Y.pt w, ?_⟩
    have h1 : d (Y.pt w) = X.pt w := by rw [← hd']; rfl
    have h2 : f (M.pt w) = X.pt w := by rw [← hf']; rfl
    exact h1.trans h2.symm
  · rw [Category.assoc, hs, ← hd.inducedModelMorphism_comp_structureMap, ← hf.inducedModelMorphism_comp_structureMap]
    simp only [← Category.assoc, he]
  · intro x hx
    have h : x ≫ e.hom = Y.pt := by
      rw [← cancel_mono d, Category.assoc, he, ← Category.assoc, hx, hf', hd']
    rw [← Category.assoc, h, hpt]

end GlobalTheory.SiegTh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenImmersionSpecRingOnAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Div.AffChart

open GlobalTheory.Points

theorem exists_openImm_spec_ringOn (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω)
    (W : M.Z.Opens) (hW : IsAffineOpen W) (hne : (W : Set M.Z).Nonempty) :
    ∃ (χ : Sp (M.ringOn W) ⟶ M.Z) (_ : IsOpenImmersion χ), χ.opensRange = W ∧
      spMap (algebraMap (M.ringOn W) Ω) ≫ χ = M.pt := by
  let φ : Γ(M.Z, W) ⟶ CommRingCat.of (M.ringOn W) := (M.sectionsEquiv W hne).toCommRingCatIso.hom
  haveI : IsIso φ := inferInstanceAs (IsIso (M.sectionsEquiv W hne).toCommRingCatIso.hom)
  refine ⟨Spec.map φ ≫ hW.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.opensRange_comp_of_isIso, hW.opensRange_fromSpec]
  · have hp := M.top_le_preimage_pt hne
    have e : φ ≫ CommRingCat.ofHom (algebraMap (M.ringOn W) Ω) = valMap M.pt W hp := by
      ext f
      exact (M.coe_sectionsEquiv W hne f).trans (M.res_apply W hne f).symm
    rw [spMap, ← Category.assoc, ← Spec.map_comp, e, specMap_valMap_fromSpec]

end GlobalTheory.Div.AffChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosuStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  first | exact @GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | exact GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | (intros; apply GlobalTheory.PrincipalBaseChange.exists_principal_algClosure <;> assumption)
end

