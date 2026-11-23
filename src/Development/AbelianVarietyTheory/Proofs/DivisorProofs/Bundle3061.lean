module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSchemeAdjointActionsAbelian
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleVerticalFieldsEqCoboundaryAddLogDeriv
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSCocycle

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.LogKSLin
open GlobalTheory.Points (valR_eq valR_add valR_mul valR_res valR_appLE le_preimage_mono)

theorem resG_resG' {Z : Scheme.{0}} {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x :=
  (congrArg (fun k => k.hom x) (Z.presheaf.map_comp (homOfLE h).op (homOfLE h').op)).symm

theorem exists_coboundary_add_dlog : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
  intro E _ _ _ H X t hP hA hK U n v hv hb J W j hWa hcov hj e he hev hcoc
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i => (le_iSup W i).trans hcov.le
  choose dd hdF hd0 hdv using fun a => exists_invField U (hv a)
  have hsp := fun i i' => _root_.GlobalTheory.VertSpan.vert_span E H X t U n v hv hb dd hdF hd0 hdv (W i ⊓ W i') (inf_le_left.trans (hWU i))
    (e i i') (he i i') (fun r => hev i i' _ r)
  choose c hc using fun i i' => (hsp i i').exists
  have hcc : ∀ a i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i' a) +
      resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
        (c i' i'' a) =
      resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
        (c i i'' a) := by
    intro a i i' i''
    have h1 : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i' := inf_le_left
    have h2 : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have h3 : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hT : W i ⊓ W i' ⊓ W i'' ≤ t.G.hom ⁻¹ᵁ U.1 := h3.trans (inf_le_left.trans (hWU i))
    have hu := (_root_.GlobalTheory.VertSpan.vert_span E H X t U n v hv hb dd hdF hd0 hdv (W i ⊓ W i' ⊓ W i'') hT (e i i'')
      (isField_mono h3 (he i i'')) (fun r => ?_)).unique
      (y₁ := fun a => resG _ h1 (c i i' a) + resG _ h2 (c i' i'' a)) (y₂ := fun a => resG _ h3 (c i i'' a)) ?_ ?_
    · exact congrFun hu a
    · rw [← resG_appLE U (inf_le_left.trans (hWU i)) h3 r, (he i i'').2.2 _ _ h3 le_rfl, hev, map_zero]
    · intro O hO f
      rw [← hcoc i i' i'' O hO f, hc i i' O (hO.trans h1) f, hc i' i'' O (hO.trans h2) f]
      simp only [map_add (f := _), resG_resG', add_mul, Finset.sum_add_distrib]
    · intro O hO f
      rw [hc i i'' O (hO.trans h3) f]
      simp only [resG_resG']
  choose θ hh hθ using fun a => _root_.GlobalTheory.CechH1Span.exists_dlog_add_coboundary E H X t hP hA hK U n v hv hb dd hdF hd0 hdv J W j hWa hcov hWU hj
    (fun i i' => c i i' a) (hcc a)
  refine ⟨Matrix.of fun a b => θ a b, fun i O f => ∑ a, smulFld (hh a i) (dd a) O f,
    fun i => isField_sum fun a => isField_smul _ (isField_mono (hWU i) (hdF a)), fun i hW r => ?_,
    fun i i' O hO f S _ φ g₀ w hg hgO hw => ?_⟩
  · simp only [smulFld_of_le le_rfl, hd0, mul_zero, Finset.sum_const_zero]
  · have hO1 : O ≤ W i := hO.trans inf_le_left
    have hO2 : O ≤ W i' := hO.trans inf_le_right
    have hPU : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1 := inf_le_left.trans (hWU i)
    have hgP : ⊤ ≤ g₀ ⁻¹ᵁ (W i ⊓ W i') := le_preimage_mono g₀ hO hgO
    have hred := fun a => translate_red (hv a) hg (hw a)
    have key : ∀ a, valR g₀ O (resG t.G.left hO (c i i' a) * dd a O f) =
        valR g₀ (W i) (hh a i) * (valR (w a) O f).snd - valR g₀ (W i') (hh a i') * (valR (w a) O f).snd +
          ∑ b, φ (θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd *
            valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := by
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [valR_mul _ _ hgO, valR_res _ hO hgO, hdv a O (hO.trans hPU) f S φ g₀ (w a) hg hgO (hw a), hθ a i i',
        valR_add _ _ hgP, GlobalTheory.CechInv.valR_sub _ _ hgP, valR_res _ _ hgP, valR_res _ _ hgP, valR_eq _ _ hgP,
        map_sum, add_mul, sub_mul, Finset.sum_mul]
      refine congrArg (_ + ·) (Finset.sum_congr rfl fun b _ => ?_)
      rw [← valR_eq _ _ hgP, valR_mul _ _ hgP, valR_mul _ _ hgP, valR_base U _ hg hgP, valR_res _ _ hgP,
        hdv b _ hPU _ S φ g₀ (w b) hg hgP (hw b),
        valR_res _ _ (GlobalTheory.CechKS.le_preimage_of_red (hred b) hgP)]
    have hsm : ∀ k (hk : O ≤ W k), valR g₀ O (∑ a, smulFld (hh a k) (dd a) O f) =
        ∑ a, valR g₀ (W k) (hh a k) * (valR (w a) O f).snd := by
      intro k hk
      set_option synthInstance.maxHeartbeats 100000 in
        rw [valR_eq _ _ hgO, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← valR_eq _ _ hgO, smulFld_of_le hk, valR_mul _ _ hgO, valR_res _ hk hgO,
        hdv a O (hk.trans (hWU k)) f S φ g₀ (w a) hg hgO (hw a)]
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc i i' O hO f, GlobalTheory.CechInv.valR_sub _ _ hgO, hsm i hO1, hsm i' hO2, valR_eq _ _ hgO, map_sum]
    simp only [← valR_eq _ _ hgO, key, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]

end GlobalTheory.KSCocycle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitPeriodsBoundedBelowClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.PerBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem eq_zero_of_sum_eq_zero (hpq : ¬ 1 ≤ Dw.p + Dw.q) (T : UTrait Xo c) (x : T.P.D.toPre.X) : x = 0 := by
  have hr := UTrait.finrank_le_min E H Dw l Xo c T
  have h0 : Module.finrank (𝓞 E) T.P.D.toPre.X = 0 := by omega
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 h0 x
  obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)
  have h : n • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hax, smul_zero]
  exact (smul_eq_zero.1 h).resolve_left hn

end GlobalTheory.UPoinc.PerBound


open GlobalTheory.UPoinc.PerBound in
theorem GlobalTheory.UPoinc.lam_of_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ p _ z₁ hz
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  swap
  · exact ⟨0, fun t x hx => absurd (eq_zero_of_sum_eq_zero hpq t.T x) hx⟩
  obtain ⟨m, X', U, hU, hcov⟩ := _root_.GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover E H Dw l Xo c C (_root_.GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at E H Dw hpq l Xo c C)
  choose K hK using fun k => _root_.GlobalTheory.UPoinc.ShortBound.main E H Dw l Xo c C (X' k) p
  choose e he1 he using fun k => _root_.GlobalTheory.UPoinc.ValBound.exists_pow_norm_val_le E H Dw l Xo c C X₁ (X' k) z₁
  refine ⟨∑ k, (e k : ℝ) * |K k|, fun t x hx => ?_⟩
  have hzc : IsClosed ({X₁.π z₁} : Set C.Z) := by
    haveI := X₁.fin
    have := X₁.π.isClosedMap _ hz
    rwa [Set.image_singleton] at this
  obtain ⟨k, w, hwU, hw⟩ := hcov ((spMap t.ι ≫ t.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)))
  have hgen : (X' k).π w = (gPt p ≫ (t.y ≫ X₁.π)) (IsLocalRing.closedPoint (PadicAlgCl p)) := by
    rw [hw, t.comm]
    rfl
  obtain ⟨y', hy'π, hy'w⟩ := _root_.GlobalTheory.UPoinc.exists_lift_finite_through_point _ _ (X' k).π (X' k).fin p (t.y ≫ X₁.π) w hgen
  have hz'π : (X' k).π (y' (cPt p)) = X₁.π z₁ := by
    have := congrArg (fun f => f (cPt p)) hy'π
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, t.cen]
  have hz'c := _root_.GlobalTheory.isClosed_singleton_of_isFinite _ _ _ (X' k).fin (y' (cPt p)) (hz'π ▸ hzc)
  let t' : UCTrait (X' k) p (y' (cPt p)) :=
    { y := y', cen := rfl, T := t.T, ι := t.ι, int := t.int, comm := by rw [hy'π]; exact t.comm }
  have hreg : (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ t'.y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
    show (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ y') (IsLocalRing.closedPoint (PadicAlgCl p)))
    rw [hy'w]
    exact (hU k).trans (RatModel.ringOn_le_O hwU)
  obtain ⟨h', hh'm, hh'⟩ := hK k (y' (cPt p)) hz'c t' hreg x hx
  obtain ⟨h, hhm, hh⟩ := he k p t (y' (cPt p)) t' hy'π.symm h' hh'm
  refine ⟨h, hhm, le_trans ?_ hh⟩
  have hs : 0 ≤ t.sc * t.T.be x x := mul_nonneg (sc_pos t).le (by exact_mod_cast (be_pos _ x hx).le)
  have hsum : (e k : ℝ) * |K k| ≤ ∑ k, (e k : ℝ) * |K k| :=
    Finset.single_le_sum (f := fun k => (e k : ℝ) * |K k|) (fun k _ => by positivity) (Finset.mem_univ k)
  have hKk : (e k : ℝ) * K k ≤ (e k : ℝ) * |K k| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  calc Real.exp (-((∑ k, (e k : ℝ) * |K k|) * (t.sc * t.T.be x x)))
      ≤ Real.exp (-(K k * (t.sc * t.T.be x x))) ^ e k := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        nlinarith
    _ ≤ ‖t'.val h'‖ ^ e k := pow_le_pow_left₀ (Real.exp_pos _).le hh' _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreLiftCommTranslationSectionRatiosStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibreLift_comm_translation_section_ratios : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (y : P.D.toPre.X) (T₀ : A₀.left ⟶ A₀.left), T₀ ≫ m₀ = m₀ ≫ (lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left → T₀ ≫ A₀.hom = A₀.hom → ∀ (N : ℕ), 1 ≤ N → ∀ (σ σ' : P.D.toPre.SecB N 0) (U : P.D.toPre.P.A.left.Opens) (f : Γ(P.D.toPre.P.A.left, U)), (∀ z ∈ U, ∀ J, Good P.D.toPre.P.L z J → IsUnit (sval σ' (𝟙 _) z J) ∧ sval σ (𝟙 _) z J = gs (𝟙 _) z U f * sval σ' (𝟙 _) z J) → dl ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U) (((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left.app U).hom f) = pbT T₀ (dl U f) (m₀ ⁻¹ᵁ ((lift (toUnit P.D.toPre.P.A ≫ P.D.toPre.c y) (𝟙 P.D.toPre.P.A) ≫ μ[P.D.toPre.P.A]).left ⁻¹ᵁ U)) := by
  first | exact @GlobalTheory.HeatRatioW.dl_comm_transl_ratio | exact GlobalTheory.HeatRatioW.dl_comm_transl_ratio | (intros; apply GlobalTheory.HeatRatioW.dl_comm_transl_ratio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAevalEqProdAroots
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem deg_aeval_eq_prod_aroots :
    ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ),
      algebraMap ℚ Ω (deg (Polynomial.aeval f R).asHom : ℚ) =
        ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map
          (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim
    (fun F => (deg (Polynomial.aeval f F).asHom : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A
      (Polynomial.aeval f G).asHom (Polynomial.aeval f F).asHom rfl rfl).2
    rw [map_mul, End.mul_asHom, h, Nat.cast_mul, mul_comm]
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous
      K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    change (deg (∑ i, m i • End.addEquiv (Polynomial.aeval f (u i))) : ℚ) =
      (deg (End.addEquiv (Polynomial.aeval f (∑ i, m i • u i))) : ℚ)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = ((n : End A) - f) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    rw [e]
    exact Int.cast_natCast _

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorStalkEvaluationLinearMapFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem sub_mem_of_sumI {V Ix : Type} [CommRing V] {I : Ideal V} {y : Ix → V} {v : V} (h : SumI I y v) (i₀ : Ix)
    (hy : ∀ j, j ≠ i₀ → y j ∈ I) : v - y i₀ ∈ I := by
  classical
  obtain ⟨N, -, -, -, hS⟩ := h
  obtain ⟨S, hS⟩ := hS 1
  have h1 := Submodule.smul_mono (le_refl (I ^ 1)) (le_top : N ≤ ⊤) (hS (insert i₀ S) (Finset.subset_insert _ _))
  rw [pow_one, smul_eq_mul, Ideal.mul_top, ← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at h1
  have h2 : ∑ j ∈ (insert i₀ S).erase i₀, y j ∈ I :=
    Submodule.sum_mem _ fun j hj => hy j (Finset.ne_of_mem_erase hj)
  have := add_mem h1 h2
  convert this using 1
  ring

private theorem sum_terms_universal_member {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X]
    {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X} (𝔪 : UMem X₁ z₁ act V ev X t δ)
    {x₀ : X₁.S.Gam} {C : Type} {lab : C → X₁.S.Gam} {T : (Fin 8 → X) → C → V} (h : 𝔪.Terms x₀ lab T) (c : C) :
    SumF (maximalIdeal V) (FractionRing V)
      (fun χ => algebraMap V (FractionRing V) (T (𝔪.e₈.symm χ) c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)
      (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩) := by
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hs, hc, hT⟩ := h
  have := (hc c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hc c).2.1 th s _ hs (hth (lab c))
  convert this using 2 with χ
  rw [hT, AddEquiv.apply_symm_apply]

theorem UMem.const_term_sub_mem : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (r : X₁.M.Z.presheaf.stalk z₁), X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ → ev1 r - T 0 c ∈ maximalIdeal V1 := by
  intro g n F W Z i X₁ z₁ act x₀ hd V _ _ _ ev X _ m t δ 𝔪 C lab hlab T hT c r hr
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hθ := UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hd
  have sp : ∀ w, X₁.M.Z.fromSpecStalk z₁ w ⤳ z₁ := fun w => by
    have : X₁.M.Z.fromSpecStalk z₁ w ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨w, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd' := hd.of_specializes
    (ξ := (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) (sp _)
  have hs : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have e := RatModel.val_mul hs (hd'.2 (lab c)) (𝔪.reg _ (X₁.S.th_mem x₀))
  rw [div_mul_cancel₀ _ hd.1, ← hr, TwistSum₂.val_stalkHom] at e
  have e' : 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ =
      algebraMap V (FractionRing V) (ev r) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    rw [𝔪.yK_eq, 𝔪.yK_eq]
    exact e
  have hS := sum_terms_universal_member 𝔪 hT c
  rw [e'] at hS
  have hI := TwistSum₂.sumI_of_sumF_mul (fun χ => T (𝔪.e₈.symm χ) c) (ev r) _ hθ hS
  have := sub_mem_of_sumI hI 0 fun j hj =>
    _root_.GlobalTheory.Poinc.Sep.HighTerms.term_mem_maximalIdeal g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 C lab hlab T hT c _ (𝔪.e₈.symm.map_ne_zero_iff.2 hj)
  simpa only [map_zero] using this

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTrace
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem linTrace_eq_neg_nextCoeff {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (g : Module.End F W) :
    LinearMap.trace F W g = -g.charpoly.nextCoeff := by
  classical
  let b := Module.finBasis F W
  rw [LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_vmap {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (A : AbVar K)
    [Module.Finite ℚ_[l] (Vl l A)] (f : End A) :
    (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l f.asHom).charpoly := by
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have key := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hl A f ((charpoly f).map (algebraMap ℤ ℚ)) (hm.map _)
    (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
    (fun n => by
      rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
      simp)
  rw [← key, Polynomial.map_map]
  congr 1

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem charpoly_tate_det_trace :
    ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A),
      (∀ [Module.Finite ℚ_[l] (Vl l A)],
        (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l f.asHom).charpoly) ∧
      (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)],
        (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧
      LinearMap.det (vmap l f.asHom) = (deg f.asHom : ℚ_[l]) ∧
      LinearMap.trace ℚ_[l] _ (vmap l f.asHom) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  refine ⟨fun {_} => charpoly_map_vmap l hl A f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
    have hc : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] := Subsingleton.elim _ _
    rw [hc]
    exact charpoly_map_vmap l hl A f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      have h : (-f).asHom = -f.asHom := map_neg (End.addEquiv (X := A)) f
      simp only [h, vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
    have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [Int.cast_zero, zero_sub, neg_neg] at hev
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← charpoly_map_vmap l hl A (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← charpoly_map_vmap l hl A f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyCloseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T], AIC T → IsUnit (q : T) → HInv q T := by
  first | (exact @GlobalTheory.HInvAic.main) | (exact GlobalTheory.HInvAic.main) | (intros; apply GlobalTheory.HInvAic.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSchemeAdjointActionsAbelianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_scheme_adjoint_actions_abelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π := by
  first | (exact @GlobalTheory.ActFin.exists_actRep_finite) | (exact GlobalTheory.ActFin.exists_actRep_finite) | (intros; apply GlobalTheory.ActFin.exists_actRep_finite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverEmbeddingClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_emb_of_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')) (C' : LabCover D') (E : Emb C'.π C'.G), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ E.Theta C'.P.L.L := by
  intro R _ _ _ hR D C
  obtain ⟨R₁, i₁, i₂, i₃, ρ, D₁, C₁, hρ, hD, hS⟩ := _root_.GlobalTheory.Mum.exists_secs_finExt R hR D C
  have := hR.2
  have h₁ : Base R₁ := ⟨hρ.1, (RingHom.charZero_iff hρ.2.1).1 this⟩
  obtain ⟨C', E, hE⟩ := _root_.GlobalTheory.Mum.SecEmb.emb_of_secs R₁ h₁ D₁ C₁ hS
  exact ⟨R₁, i₁, i₂, i₃, ρ, D₁, C', E, hρ, hD, hE⟩
end

