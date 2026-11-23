module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalRingCardinality.SpanPowerMembership.Places
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuation
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVal

open GlobalTheory.IdemSupport

theorem valuation_cP {D : D7} (Q : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.E) :
    (cP Q).valuation D.host.E (star x) = Q.valuation D.host.E x := by
  have : cP Q = Formalism.BasicNotions.Examples₂.PlacesToy.conjW Q := by
    ext r
    have := Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow Q r 1
    rw [pow_one, pow_one] at this
    rw [this, mem_cP]
    rfl
  rw [this, Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW, star_star]

theorem eq_of_le_iff {a b : WithZero (Multiplicative ℤ)}
    (h : ∀ c, c ≠ 0 → (a ≤ c ↔ b ≤ c)) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, (∀ c, c ≠ 0 → a ≤ c → b ≤ c) → b ≤ a := by
    intro a b h
    by_cases ha : a = 0
    · by_contra hb
      have hb0 : b ≠ 0 := fun e => hb (by rw [e]; exact zero_le)
      have h1 := h (WithZero.exp (WithZero.log b - 1)) WithZero.exp_ne_zero (by rw [ha]; exact zero_le)
      rw [← WithZero.exp_log hb0, WithZero.exp_le_exp, WithZero.log_exp] at h1
      omega
    · exact h a ha le_rfl
  exact le_antisymm (key fun c hc => (h c hc).2) (key fun c hc => (h c hc).1)

theorem int_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {e : FiniteAdeleRing (𝓞 E) E}
    (h1 : e P = 1) (h0 : ∀ R, R ≠ P → e R = 0) (y : FiniteAdeleRing (𝓞 E) E) {k : E} (hk : k ≠ 0) :
    (∀ R : HeightOneSpectrum (𝓞 E), Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R) ≤ 1) ↔
      Valued.v (y P) ≤ P.valuation E k := by
  have e1 : ∀ R, (e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R =
      e R * (y R * algebraMap E (R.adicCompletion E) k⁻¹) := fun R => rfl
  have hv : 0 < P.valuation E k := zero_lt_iff.2 (by simpa using hk)
  have e2 : Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) P) ≤ 1 ↔
      Valued.v (y P) ≤ P.valuation E k := by
    rw [e1, h1, one_mul, map_mul, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, mul_inv_le_iff₀ hv, one_mul]
  rw [← e2]
  refine ⟨fun h => h P, fun h R => ?_⟩
  by_cases hR : R = P
  · rw [hR]; exact h
  · rw [e1, h0 R hR, zero_mul, map_zero]
    exact zero_le

theorem map_three {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B ≃+* C) (a b c : A) :
    g (f (a * (b * c))) = g (f a) * (g (f b) * g (f c)) := by
  simp only [map_mul]

theorem conj_mem_iff {D : D7} (e z : AE D) (k : D.host.E) :
    finPart D (cA D e * (cA D z * incA D (star k)⁻¹)) ∈ intAE D ↔ finPart D (e * (z * incA D k⁻¹)) ∈ intAE D := by
  rw [← star_inv₀, ← cA_incA, ← RingHom.map_mul, ← RingHom.map_mul]
  refine ⟨fun h => ?_, finPart_cA_mem⟩
  have := finPart_cA_mem h
  rwa [cA_cA] at this


set_option maxHeartbeats 800000 in
theorem components_and_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  intro D ι hinc hint hid
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  choose ε hε using hid
  have hd : ∀ P, IsDelta Φ P (ε P) := fun P => (tie_iff hΦ (hε P).1.1 (hε P).2.1 P).1 (hε P).1.2.2
  refine ⟨fun e P h => ?_, fun z Q => ?_⟩
  · rw [delta_unique hΦ (delta_of_isIdemAt hΦ h) (hd P)]
    exact (hε P).2
  have hc : cA D (ε Q) = ε (cP Q) := delta_unique hΦ (delta_conj hΦ (hd Q)) (hd _)
  have key : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : AE D) (k : D.host.E), k ≠ 0 →
      (finPart D (ε P * (y * incA D k⁻¹)) ∈ intAE D ↔ Valued.v (ι (finPart D y) P) ≤ P.valuation D.host.E k) := by
    intro P y k hk
    have : ι (finPart D (incA D k⁻¹)) = algebraMap D.host.E _ k⁻¹ := hinc k⁻¹
    rw [hint, map_three, this]
    exact int_iff (hε P).2.2.1 (hε P).2.2.2 _ hk
  refine eq_of_le_iff fun c hc0 => ?_
  obtain ⟨k, rfl⟩ := Q.valuation_surjective D.host.E c
  have hk : k ≠ 0 := fun e => hc0 (by rw [e, Valuation.map_zero])
  have h1 := key (cP Q) (cA D z) (star k) (star_ne_zero.2 hk)
  rw [valuation_cP, ← hc, conj_mem_iff] at h1
  exact h1.symm.trans (key Q z k hk)

end GlobalTheory.ConjVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCover
section
noncomputable section

namespace GlobalTheory.FiniteAmpleFP

open Polynomial CategoryTheory GlobalTheory.FiniteAmple

section Algebra

variable {A B : Type} [CommRing A] [CommRing B]

theorem exists_finFree_away_fp {φ : A →+* B} (hf : φ.Finite) (hfl : φ.Flat) (hfp : φ.FinitePresentation)
    (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, ∀ {A' B' : Type} [CommRing A'] [CommRing B'] {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'},
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
      IsUnit (α r) → FinFree φ' := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Free (Localization p.asIdeal.primeCompl) (LocalizedModule p.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B) (Localization p.asIdeal.primeCompl)
  refine ⟨r, hr, ?_⟩
  intro A' B' _ _ α β φ' H hu
  algebraize [α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  refine ⟨Module.Finite.equiv hb.equiv, ?_⟩
  letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r (g := α) hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  have h₁ : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) B)).equiv.symm
  exact Module.Free.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B).trans hb.equiv)

end Algebra

section Geometry

open AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

theorem exists_finFree_app_fp [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (f.app V).hom := by
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset hx
  have hfl : (f.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.flat_appLE hV (hV.preimage f) _
  have hfp : (f.app V).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE @LocallyOfFinitePresentation f ‹_› ⟨V, hV⟩ ⟨_, hV.preimage f⟩ _
  obtain ⟨r, hr, H⟩ := exists_finFree_away_fp (f.finite_app V hV) hfl hfp (hV.primeIdealOf ⟨x, hxV⟩)
  refine ⟨X.basicOpen r, hV.basicOpen r, ?_, (X.basicOpen_le r).trans hle,
    H (isPushout_app f hV (hV.basicOpen r) (X.basicOpen_le r)) (X.toRingedSpace.isUnit_res_basicOpen r)⟩
  have e := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have h₁ : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen]
    exact hr
  exact (congrArg (· ∈ X.basicOpen r) e).mp h₁

theorem exists_sec_image_nonzeroLocus_fp [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {M : LB X} (hM : M.IsLB)
    (t : (M.pull f).Sec) : ∃ u : ∀ k, (lbPow M k).Sec, ∀ x : X,
      (∃ y ∈ nonzeroLocus t, f y = x) ↔ ∃ k, 1 ≤ k ∧ x ∈ nonzeroLocus (u k) := by
  let α : Type := {p : X.Opens × M.ι // IsAffineOpen p.1 ∧ p.1 ≤ M.U p.2 ∧ FinFree (f.app p.1).hom}
  have cov : ∀ x : X, ∃ a : α, x ∈ a.1.1 := fun x => by
    obtain ⟨i, hi⟩ := exists_chart hM x
    obtain ⟨V, hV, hx, hle, hF⟩ := exists_finFree_app_fp f hi
    exact ⟨⟨(V, i), hV, hle, hF⟩, hx⟩
  have le : ∀ a : α, f ⁻¹ᵁ a.1.1 ≤ (M.pull f).U fun _ => a.1.2 := fun a y hy => mem_pull.2 (a.2.2.1 hy)
  let τ : ∀ a : α, Γ(Y, f ⁻¹ᵁ a.1.1) := fun a => resG Y (le a) (t.f fun _ => a.1.2)
  let c : ∀ (k : ℕ) (a : α), Γ(X, a.1.1) := fun k a => (revChar _ a.2.2.2 (τ a)).coeff k
  have key : ∀ k (x : X) (a b : α), x ∈ a.1.1 → x ∈ b.1.1 → gs (𝟙 X) x _ (c k a) =
      (gm (𝟙 X) x (M.U a.1.2 ⊓ M.U b.1.2) (M.g a.1.2 b.1.2)).val ^ k * gs (𝟙 X) x _ (c k b) := by
    intro k x a b ha hb
    obtain ⟨W, hW, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := a.1.1 ⊓ b.1.1) (x := x) ⟨ha, hb⟩
    have hle : W ≤ a.1.1 ⊓ b.1.1 := hle
    have la : W ≤ a.1.1 := hle.trans inf_le_left
    have lb : W ≤ b.1.1 := hle.trans inf_le_right
    have lg : W ≤ M.U a.1.2 ⊓ M.U b.1.2 := le_inf (la.trans a.2.2.1) (lb.trans b.2.2.1)
    have : Nonempty W := ⟨⟨x, hx⟩⟩
    obtain ⟨hF, ea⟩ := finFree_revChar_of_isPushout (isPushout_app f a.2.1 hW la) a.2.2.2
    have ea := congrArg (fun p => p.coeff k) (ea hF (τ a))
    have eb := congrArg (fun p => p.coeff k)
      ((finFree_revChar_of_isPushout (isPushout_app f b.2.1 hW lb) b.2.2.2).2 hF (τ b))
    simp only [coeff_map] at ea eb
    have eτ : resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ a.1.1 from fun _ hy => la hy) (τ a) =
        (f.app W).hom (resG X lg (M.g a.1.2 b.1.2).val) *
          resG Y (show f ⁻¹ᵁ W ≤ f ⁻¹ᵁ b.1.1 from fun _ hy => lb hy) (τ b) := fn_ext fun y hy => by
      have hy' : (𝟙 Y ≫ f) y ∈ W := hy
      rw [gs_mul (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y (le a) (la hy),
        gs_res (𝟙 Y) y (le b) (lb hy), gs_pull (𝟙 Y) f y W hy, gs_res (𝟙 Y ≫ f) y _ hy',
        gs_unit (𝟙 Y ≫ f) y _ (lg hy'),
        ← gm_pull_g M f (𝟙 Y) y (fun _ => a.1.2) (fun _ => b.1.2) (le a (la hy)) (le b (lb hy))]
      exact gs_compat t (𝟙 Y) y (le a (la hy)) (le b (lb hy))
    have e : resG X la (c k a) = resG X lg (M.g a.1.2 b.1.2).val ^ k * resG X lb (c k b) :=
      ea.symm.trans ((congrArg (fun z => (revChar _ hF z).coeff k) eτ).trans
        ((coeff_revChar_mul _ hF _ _ k).trans (congrArg (_ * ·) eb)))
    have e' := congrArg (gs (𝟙 X) x W) e
    rwa [gs_mul _ x _ hx, gs_pow _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit _ x _ (lg hx)] at e'
  choose u hu using fun k => exists_sec_of_refinement (isLB_lbPow hM k) (fun a : α => a.1.1)
    (fun a _ => a.1.2) (fun a x hx => mem_powChart.2 (a.2.2.1 hx)) cov (c k) fun x a b ha hb => by
      rw [gm_lbPow_g k (𝟙 X) x _ _ (mem_powChart.2 (a.2.2.1 ha)) (mem_powChart.2 (b.2.2.1 hb)),
        Units.val_pow_eq_pow_val]
      exact key k x a b ha hb
  refine ⟨u, fun x => ?_⟩
  obtain ⟨a, ha⟩ := cov x
  have loc : ∀ k, x ∈ nonzeroLocus (u k) ↔ x ∈ X.basicOpen (c k a) := fun k => by
    have hJ : x ∈ (lbPow M k).U fun _ => a.1.2 := mem_powChart.2 (a.2.2.1 ha)
    rw [mem_nonzeroLocus_iff_isUnit (u k) hJ, hu k x _ a hJ ha, Units.isUnit_units_mul]
    exact isUnit_gs_iff (𝟙 X) x _ ha _
  simp only [loc]
  rw [← mem_image_basicOpen_app f a.2.1 a.2.2.2 (τ a) ha]
  refine exists_congr fun y => and_congr_left fun e => ?_
  have hy : y ∈ f ⁻¹ᵁ a.1.1 := show f y ∈ a.1.1 from e ▸ ha
  rw [mem_nonzeroLocus_iff_isUnit t (le a hy), ← gs_res (𝟙 Y) y (le a) hy]
  exact isUnit_gs_iff (𝟙 Y) y _ hy _

theorem isAmpleLB_of_pull_fp [IsFinite f] [Flat f] [Surjective f] [LocallyOfFinitePresentation f] {L : LB X} (hL : L.IsLB)
    (h : IsAmpleLB (L.pull f)) : IsAmpleLB L := by
  have := h.compactSpace
  have : CompactSpace X := f.surjective.compactSpace f.continuous
  refine isAmpleLB_of_forall_le hL fun x U hx => ?_
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨n, hn, s, hs, hle, -⟩ := h.exists_affine_le (x := y) (U := f ⁻¹ᵁ U) hx
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull (isLB_lbPow hL n) f) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL f n).symm s
  obtain ⟨u, hu⟩ := exists_sec_image_nonzeroLocus_fp f (isLB_lbPow hL n) t
  obtain ⟨k, hk, hy⟩ := (hu (f y)).1 ⟨y, ht.ge hs, rfl⟩
  have e := nonzeroLocus_secOfPowPow (u k)
  refine ⟨n * k, Nat.mul_pos hn hk, secOfPowPow (u k), e.ge hy, fun z hz => ?_⟩
  obtain ⟨w, hw, rfl⟩ := (hu z).2 ⟨k, hk, e.le hz⟩
  exact hle (ht.le hw)

end Geometry

end GlobalTheory.FiniteAmpleFP

namespace GlobalTheory.HeckeAmple

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory

theorem relAmple_of_pull_hom {S : Scheme.{0}} {A B : Over S} [GrpObj B] (hB : IsAbelianScheme B) (ψ : A ⟶ B)
    [IsFinite ψ.left] [Flat ψ.left] [Surjective ψ.left] [LocallyOfFinitePresentation ψ.left]
    {M : LB B.left} (hM : M.IsLB) (hA : Out.RelAmple A (M.pull ψ.left)) : Out.RelAmple B M := by
  refine relAmple_of_isAbelianScheme B hB hM fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple A (LB.isLB_pull hM _) hA U hU
  have pre : A.hom ⁻¹ᵁ U = ψ.left ⁻¹ᵁ (B.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, Over.w ψ]
  rw [pre] at h₁
  have h₃ : IsAmpleLB ((M.pull (B.hom ⁻¹ᵁ U).ι).pull (ψ.left ∣_ (B.hom ⁻¹ᵁ U))) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM _) _) (LB.isLB_pull (LB.isLB_pull hM _) _)
      (FiniteAmple.lbIso_pull_pull _ hM (morphismRestrict_ι ψ.left _).symm)).1 h₁
  have : Surjective (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @Surjective) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : IsFinite (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : Flat (ψ.left ∣_ B.hom ⁻¹ᵁ U) := MorphismProperty.of_isPullback (P := @Flat) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  have : LocallyOfFinitePresentation (ψ.left ∣_ B.hom ⁻¹ᵁ U) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_morphismRestrict ψ.left _).flip inferInstance
  exact FiniteAmpleFP.isAmpleLB_of_pull_fp _ (LB.isLB_pull hM _) h₃

theorem relAmple_diag_of_galois : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ), 1 ≤ m → ∀ (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) := by
  intro p _ D R _ b M S s o A' _ _ ψ G hA' _ hG m hm P' hP' hw
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have : Flat ψ.left := inferInstance
  have : LocallyOfFinitePresentation ψ.left := inferInstance
  have hP := o.isLB
  have e : ψ.left ≫ (lift (𝟙 A') (𝟙 A')).left = (lift (𝟙 o.A) (𝟙 o.A)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have hL' : (P'.pull (lift (𝟙 A') (𝟙 A')).left).IsLB := LB.isLB_pull hP' _
  refine relAmple_of_pull_hom hA' ψ hL' ?_
  have hLd : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull hP _
  have H₁ := FiniteAmple.lbIso_pull_pull (lift (𝟙 A') (𝟙 A')).left hP' e
  have H₂ : LBIso ((P'.pull (Hecke.sq2 ψ)).pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left) :=
    LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hw.symm
  have H₃ : LBIso ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left)
      (LB.LinComb o.P (K := Fin m) (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1)) :=
    lbIso_of_chartPull (chartPullOut o.P (fun _ => 𝟙 _) (fun _ => 1) (lift (𝟙 o.A) (𝟙 o.A)).left
      (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) fun _ => (Category.comp_id _).symm) (LB.isLB_linComb hP _ _)
  have H₄ := (lbIso_lbPow_finPow hP (lift (𝟙 o.A) (𝟙 o.A)).left m).symm
  have hLB₁ := LB.isLB_pull hL' ψ.left
  have hLB₂ : ((P'.pull (Hecke.sq2 ψ)).pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull (LB.isLB_pull hP' _) _
  have hLB₃ : ((Hecke.lbPow o.P m).pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB :=
    LB.isLB_pull (LB.isLB_linComb hP _ _) _
  have hLB₄ := LB.isLB_linComb hP (K := Fin m) (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1)
  have hLB₅ := isLB_lbPow hLd m
  have H : LBIso ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) (lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) m) :=
    LBIso.trans hLB₁ hLB₄ hLB₅ (LBIso.trans hLB₁ hLB₃ hLB₄ (LBIso.trans hLB₁ hLB₂ hLB₃ H₁ H₂) H₃) H₄
  refine relAmple_of_isAbelianScheme o.A o.ab hLB₁ fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple o.A hLd o.ample U hU
  have h₂ := (isAmpleLB_pow_iff (LB.isLB_pull hLd (o.A.hom ⁻¹ᵁ U).ι) hm).2 h₁
  have h₃ := h₂.of_lbIso (LB.isLB_pull hLB₅ _) (lbIso_lbPow_pull hLd (o.A.hom ⁻¹ᵁ U).ι m).symm
  exact h₃.of_lbIso (LB.isLB_pull hLB₁ _) (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) H)

end GlobalTheory.HeckeAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationNormOneSplitQuaternionAlgebra
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F] [NumberField F] {a b : F}

def qi : ℍ[F, a, b] := ⟨0, 1, 0, 0⟩

def qj : ℍ[F, a, b] := ⟨0, 0, 1, 0⟩

def qk : ℍ[F, a, b] := ⟨0, 0, 0, 1⟩

theorem decomp (y : ℍ[F, a, b]) : y = y.re • (1 : ℍ[F, a, b]) + y.imI • qi + y.imJ • qj + y.imK • qk := by
  ext <;> simp [qi, qj, qk]

theorem map_smul_F (c : F) (M : Matrix (Fin 2) (Fin 2) F) :
    (c • M).map (algebraMap F (AF F)) = algebraMap F (AF F) c • M.map (algebraMap F (AF F)) := by
  ext i j; simp

theorem map_smul_one (c : F) :
    (c • (1 : Matrix (Fin 2) (Fin 2) F)).map (algebraMap F (AF F)) = algebraMap F (AF F) c • 1 := by
  rw [map_smul_F, Matrix.map_one _ (map_zero _) (map_one _)]

variable (φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F)

def bcBasis : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) (AF F)) (algebraMap F (AF F) a) 0
    (algebraMap F (AF F) b) where
  i := (φ qi).map (algebraMap F (AF F))
  j := (φ qj).map (algebraMap F (AF F))
  k := (φ qk).map (algebraMap F (AF F))
  i_mul_i := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qi = a • 1 := by ext <;> simp [qi]
    rw [this, map_smul, map_one, map_smul_one, zero_smul, add_zero]
  j_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qj : ℍ[F, a, b]) * qj = b • 1 := by ext <;> simp [qj]
    rw [this, map_smul, map_one, map_smul_one]
  i_mul_j := by
    rw [← Matrix.map_mul, ← map_mul]
    have : (qi : ℍ[F, a, b]) * qj = qk := by ext <;> simp [qi, qj, qk]
    rw [this]
  j_mul_i := by
    rw [← Matrix.map_mul, ← map_mul, zero_smul, zero_sub]
    have : (qj : ℍ[F, a, b]) * qi = -qk := by ext <;> simp [qi, qj, qk]
    rw [this, map_neg, Matrix.map_neg _ (map_neg _)]

def Φ : DA F a b →ₐ[AF F] Matrix (Fin 2) (Fin 2) (AF F) := (bcBasis φ).liftHom

theorem Φ_apply (x : DA F a b) : Φ φ x = x.re • (1 : Matrix (Fin 2) (Fin 2) (AF F))
    + x.imI • (φ qi).map (algebraMap F (AF F)) + x.imJ • (φ qj).map (algebraMap F (AF F))
    + x.imK • (φ qk).map (algebraMap F (AF F)) := by
  simp [Φ, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift, bcBasis, Algebra.algebraMap_eq_smul_one]

def Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : DA F a b :=
  ∑ i, ∑ j, m i j • rat (φ.symm (Matrix.single i j 1))

theorem rat_add (x y : ℍ[F, a, b]) : rat (x + y) = rat x + rat y := by ext <;> simp [rat]

theorem rat_smul (c : F) (x : ℍ[F, a, b]) : rat (c • x) = algebraMap F (AF F) c • rat x := by
  ext <;> simp [rat] <;> rw [Algebra.smul_def]

theorem rat_sum {ι : Type} (s : Finset ι) (f : ι → ℍ[F, a, b]) : rat (∑ i ∈ s, f i) = ∑ i ∈ s, rat (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp [rat]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, rat_add, ih]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by ext <;> simp [rat]

theorem Ψ_add (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m + n) = Ψ φ m + Ψ φ n := by
  simp only [Ψ, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem Ψ_smul (c : AF F) (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (c • m) = c • Ψ φ m := by
  simp only [Ψ, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem Ψ_map (M : Matrix (Fin 2) (Fin 2) F) : Ψ φ (M.map (algebraMap F (AF F))) = rat (φ.symm M) := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single M]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Ψ, Matrix.map_apply, map_sum, rat_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (M i j) = M i j • Matrix.single i j (1 : F) by rw [Matrix.smul_single, smul_eq_mul, mul_one],
    map_smul, rat_smul]

theorem Ψ_one : Ψ φ 1 = 1 := by
  rw [← Matrix.map_one (algebraMap F (AF F)) (map_zero _) (map_one _), Ψ_map, map_one, rat_one]

theorem Φ_rat (y : ℍ[F, a, b]) : Φ φ (rat y) = (φ y).map (algebraMap F (AF F)) := by
  conv_rhs => rw [decomp y]
  simp only [Φ_apply, map_add (f := _), map_smul, map_one, Matrix.map_add (f := _), map_smul_F, Matrix.map_one _ (map_zero _) (map_one (algebraMap F (AF F)))]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul, rat]
  split_ifs <;> simp

theorem Φ_Ψ (m : Matrix (Fin 2) (Fin 2) (AF F)) : Φ φ (Ψ φ m) = m := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single m]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Ψ, map_sum, map_smul, Φ_rat, AlgEquiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ext k l; simp [Matrix.single_apply]

theorem Ψ_Φ (x : DA F a b) : Ψ φ (Φ φ x) = x := by
  rw [Φ_apply, Ψ_add, Ψ_add, Ψ_add, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_smul, Ψ_one, Ψ_map, Ψ_map, Ψ_map]
  simp only [AlgEquiv.symm_apply_apply]
  ext <;> simp [rat, qi, qj, qk]

theorem Ψ_mul (m n : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m * n) = Ψ φ m * Ψ φ n := by
  conv_lhs => rw [← Φ_Ψ φ m, ← Φ_Ψ φ n, ← map_mul, Ψ_Φ]

theorem det_four {R : Type} [CommRing R] (A₀ A₁ A₂ A₃ : Matrix (Fin 2) (Fin 2) R) (x₀ x₁ x₂ x₃ : R) :
    (x₀ • A₀ + x₁ • A₁ + x₂ • A₂ + x₃ • A₃).det = x₀ ^ 2 * A₀.det + x₁ ^ 2 * A₁.det + x₂ ^ 2 * A₂.det
      + x₃ ^ 2 * A₃.det + x₀ * x₁ * ((A₀ + A₁).det - A₀.det - A₁.det) + x₀ * x₂ * ((A₀ + A₂).det - A₀.det - A₂.det)
      + x₀ * x₃ * ((A₀ + A₃).det - A₀.det - A₃.det) + x₁ * x₂ * ((A₁ + A₂).det - A₁.det - A₂.det)
      + x₁ * x₃ * ((A₁ + A₃).det - A₁.det - A₃.det) + x₂ * x₃ * ((A₂ + A₃).det - A₂.det - A₃.det) := by
  simp [Matrix.det_fin_two]; ring

theorem det_Φ (hφ : ∀ x, (φ x).det = nrm x) (x : DA F a b) : (Φ φ x).det = nrm x := by
  have hd : ∀ y : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F))).det = algebraMap F (AF F) (nrm y) := by
    intro y; rw [← hφ y, RingHom.map_det]; rfl
  have hd2 : ∀ y z : ℍ[F, a, b], ((φ y).map (algebraMap F (AF F)) + (φ z).map (algebraMap F (AF F))).det
      = algebraMap F (AF F) (nrm (y + z)) := by
    intro y z; rw [← Matrix.map_add _ (map_add _), ← map_add (f := _)]; exact hd _
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (AF F)) = (φ 1).map (algebraMap F (AF F)) := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Φ_apply, h1, det_four]
  simp only [hd2, hd]
  simp [nrm, qi, qj, qk]
  ring

theorem nrm_Ψ (hφ : ∀ x, (φ x).det = nrm x) (m : Matrix (Fin 2) (Fin 2) (AF F)) : nrm (Ψ φ m) = m.det := by
  rw [← det_Φ φ hφ, Φ_Ψ]

theorem Ψ_cont : Continuous (Ψ φ) := by
  have hc : ∀ x : DA F a b, coords x = QuaternionAlgebra.linearEquivTuple _ _ _ x := fun x => by
    ext k; fin_cases k <;> rfl
  apply continuous_induced_rng.2
  have : (coords ∘ Ψ φ : Matrix (Fin 2) (Fin 2) (AF F) → Fin 4 → AF F) =
      fun m => ∑ i, ∑ j, m i j • coords (rat (φ.symm (Matrix.single i j 1)) : DA F a b) := by
    funext m; simp only [Function.comp, Ψ, hc, map_sum, map_smul]
  rw [this]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_id.matrix_elem i j).smul continuous_const

theorem Ψ_sub_one (m : Matrix (Fin 2) (Fin 2) (AF F)) : Ψ φ (m - 1) = Ψ φ m - 1 := by
  rw [sub_eq_add_neg, Ψ_add, show -(1 : Matrix (Fin 2) (Fin 2) (AF F)) = (-1 : AF F) • 1 by simp, Ψ_smul, Ψ_one]
  simp [sub_eq_add_neg]

end GlobalTheory.QSA.Split


open GlobalTheory.QSA.Split in
theorem GlobalTheory.QSA.strongApprox_split : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hiso S₁ S₂ ε hε hS g hg
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.quaternion_split_of_isotropic F a b ha hb hiso
  have hdet : (Φ φ g).det = 1 := by rw [det_Φ φ hφ, hg]
  have hcl := _root_.GlobalTheory.StrongApproximationSL2.strongApprox_SL2 F S₁ S₂ ε hε hS (Φ φ g) hdet
  rw [← Ψ_Φ φ g]
  refine map_mem_closure (Ψ_cont φ) hcl ?_
  rintro _ ⟨γ, hγ, h, hh, hεh, rfl⟩
  refine ⟨φ.symm γ, ?_, Ψ φ h, ?_, ?_, ?_⟩
  · rw [← hφ, AlgEquiv.apply_symm_apply, hγ]
  · rw [nrm_Ψ φ hφ, hh]
  · rw [← Ψ_sub_one, ← Ψ_smul, hεh]
  · rw [Ψ_mul, Ψ_map]
end
end

