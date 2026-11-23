module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1937
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

section IntCone

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem intCone_evalZ_sum {n : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (h : φ.LinearOn β) (a : Fin n → ℕ) :
    φ.evalZ (∑ i, a i • β i) = ∑ i, (a i : ℝ) * φ.evalZ (β i) := by
  have := h (fun i => (a i : ℝ)) (fun i => Nat.cast_nonneg _)
  refine Eq.trans ?_ this
  unfold InvFun.evalZ
  congr 1
  funext x y
  simp [LinearMap.sum_apply]

theorem intCone_absorb {n s : ℕ} {β : Fin n → LinearMap.BilinForm ℤ X} (hβ : ∀ i, β i ∈ balForms bar X)
    (hβp : ∀ i y, 0 ≤ β i y y) (hβl : φ.LinearOn β) {δ : Fin s → LinearMap.BilinForm ℤ X} (hδ : IsCone bar φ δ)
    (a : Fin n → ℕ) (b : Fin s → ℕ) (h : ∑ i, a i • β i = ∑ l, b l • δ l) (i : Fin n) (hi : 0 < a i) :
    ∃ (k : ℕ) (e : Fin s → ℕ), 0 < k ∧ k • β i = ∑ l, e l • δ l := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict
  refine h3 (β i) (hβ i) (hβp i) ?_
  have hx1 : (ℓ (∑ i, a i • β i) : ℝ) = N * ∑ i, (a i : ℝ) * φ.evalZ (β i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← intCone_evalZ_sum hβl, h, intCone_evalZ_sum hδ.linear, map_sum, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, h1]
    ring
  have hx2 : (ℓ (∑ i, a i • β i) : ℝ) = ∑ i, (a i : ℝ) * ℓ (β i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_nsmul]
  have hle : ∀ j, (a j : ℝ) * (N * φ.evalZ (β j)) ≤ (a j : ℝ) * ℓ (β j) := fun j =>
    mul_le_mul_of_nonneg_left (h2 _ (hβ j) (hβp j)) (Nat.cast_nonneg _)
  have hsum : ∑ j, ((a j : ℝ) * ℓ (β j) - (a j : ℝ) * (N * φ.evalZ (β j))) = 0 := by
    rw [Finset.sum_sub_distrib, ← hx2, hx1, Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j _ => by ring
  have ht := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hle j))).1 hsum i (Finset.mem_univ _)
  have hai : (a i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  have h4 : (a i : ℝ) * (ℓ (β i) - N * φ.evalZ (β i)) = 0 := by rw [mul_sub]; exact ht
  have h5 := (mul_eq_zero.1 h4).resolve_left hai
  linarith

theorem intCone_face : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X], IsPolFanOn bar φ X → ∀ (r r' : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X)
    (γ' : Fin r' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCone bar φ γ' → ∀ (c : Fin r → ℕ) (c' : Fin r' → ℕ),
    (∀ j, 0 < c j) → ∑ j, c j • γ j = ∑ j, c' j • γ' j → ∀ j, ∃ j', γ j = γ' j' := by
  intro O _ bar φ X _ _ _ _ r r' γ γ' hγ hγ' c c' hc he j
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hγ.mem hγ.nonneg hγ.linear hγ' c c' he j (hc j)
  have hd' : ∑ i, d i • γ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • γ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • γ' i = ∑ l, e l • γ l :=
    fun i hi => intCone_absorb hγ'.mem hγ'.nonneg hγ'.linear hγ d _ hd' i hi
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  obtain ⟨g, hg⟩ := hγ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨γ l, hγ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨γ' i, hγ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • γ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hγ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← mul_assoc, ← h2, mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

end IntCone

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDescentEtaleCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SmoothDescent

theorem smoothOfRelativeDimension_of_etale_cover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (s : Y ⟶ Sp K) (d : ℕ), Etale π → Surjective π → LocallyOfFiniteType s → SmoothOfRelativeDimension d (π ≫ s) → SmoothOfRelativeDimension d s := by
  intro K _ _ X Y π s d _ _ _ hd
  have : Smooth (π ≫ s) := SmoothOfRelativeDimension.smooth d _
  have : Smooth s := smooth_of_comp_of_etale_of_surjective π s
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  choose n W hW hn using H1.exists_dim s
  have key (y : Y) : n y = d := by
    obtain ⟨x, rfl⟩ := π.surjective y
    have := hn (π x)
    have h₁ : SmoothOfRelativeDimension (0 + n (π x)) ((π ∣_ W (π x)) ≫ (W (π x)).ι ≫ s) := inferInstance
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc] at h₁
    have h₂ : SmoothOfRelativeDimension (0 + d) ((π ⁻¹ᵁ W (π x)).ι ≫ π ≫ s) := inferInstance
    simpa using H1.dim_unique _ h₁ h₂ ⟨x, hW (π x)⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W ?_ fun y => key y ▸ hn y
  rw [← top_le_iff]
  rintro y -
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩

end GlobalTheory.SmoothDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZNonnegAway
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.CovInt


set_option maxHeartbeats 1000000 in
theorem smul_intZ_nonneg_away : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ^ 2 ∣ d.l₂.M) →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la hla v hv
  have hroot1 : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k),
      evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1 := fun k _ _ y₂ => by rw [pow_one]; exact hroot k y₂
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    exacts [h.choose_spec.1, one_ne_zero]
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, P₀ = (NumberField.discr D.host.E).natAbs := ⟨_, rfl⟩
  have hP0 : P₀ ≠ 0 := hP₀ ▸ Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = P₀ ^ Formalism.L2.Pj.DF Dw w * d.l₂.M ^ Formalism.L2.Pj.DF Dw w *
    Nat.card (Fin n → LevQ Dw d.l₂) := ⟨_, rfl⟩
  have hK0 : K ≠ 0 := hK ▸ mul_ne_zero (mul_ne_zero (pow_ne_zero _ hP0) (pow_ne_zero _ hM0)) hc0
  have hKZ : intZ D Dw d.l₂ n w = K := by rw [intZ, hK, hP₀]; ring
  rw [hKZ, mul_comm]
  obtain ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩ := hv
  show 0 ≤ nval Tc.V e (evI yI _)
  rw [evI_smul]
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot1 Λ N hU hTM hN w P hP x0 g hsec hR
      Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have heR : (0 : ℝ) < ((r * e : ℕ) : ℝ) := by exact_mod_cast he'
  rw [← nval_bc iT hr hiT e, map_mul, hval, ← hio]
  obtain ⟨ℓ, hℓ, hu⟩ := GlobalTheory.ShortBound.exists_resChar T' hfr
  have hmem : (ℓ : 𝓞 c.F) ∈ la.asIdeal := by
    by_contra hnm
    have h2 := ho'.2 (ℓ : c.F)
    have hv1 : la.valuation c.F (ℓ : c.F) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
      exact la.valuation_eq_one_iff_notMem.2 hnm
    have hv0 : vLa la (ℓ : c.F) = 0 := by simp [vLa, hv1]
    rw [map_natCast, hv0, mul_zero] at h2
    have h0 : (ℓ : T'.V) ≠ 0 := fun h0 => by
      have : algebraMap T'.V T'.Fr (ℓ : T'.V) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at this
      exact hℓ.ne_zero (by exact_mod_cast this)
    have h3 := GlobalTheory.PlaceExtField.vV_pos (K' := T'.Fr) h0 hu
    rw [map_natCast] at h3
    omega
  have hsq : ¬ ℓ ^ 2 ∣ d.l₂.M := hla ℓ hℓ hmem
  obtain ⟨α, hαM, hα⟩ : ∃ α : ℕ, α ∣ d.l₂.M ∧ ((¬ ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = 1) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) * H.bar α = (ℓ : 𝓞 D.host.E) ∧ d.l₂.Mb ≤ Ideal.span {H.bar α}) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = (ℓ : 𝓞 D.host.E))) := by
    by_cases hd : ℓ ∣ d.l₂.M
    · exact ⟨ℓ, hd, Or.inr (Or.inr ⟨hd, rfl⟩)⟩
    · exact ⟨1, one_dvd _, Or.inl ⟨hd, Nat.cast_one⟩⟩
  obtain ⟨α', hα'⟩ := hαM
  have ha0 : α ≠ 0 := left_ne_zero_of_mul (hα' ▸ hM0)
  have ha0' : α' ≠ 0 := right_ne_zero_of_mul (hα' ▸ hM0)
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) ≠ 0 :=
    (map_ne_zero io₂).2 (nrm_ne_zero _ _ (Nat.cast_ne_zero.2 ha0))
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ (d.w x0 q)) _ ζ _
    ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) _ 1 one_pos hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi x0 q)) _
    (fun q => GlobalTheory.SupFull.class_bound d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hTM hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi
      (fun b => levRep (q b)) (htp q) (hF q) hrat hsq α hα)
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hKv := add_le_add (le_refl (nval T'.V (r * e) (K : T'.Fr))) key
  rw [← nval_mul, nval_of_ne (Nat.cast_ne_zero.2 hK0), ← EReal.coe_add] at hKv
  refine le_trans (EReal.coe_nonneg.2 ?_) (hKv.trans (le_of_eq ?_))
  · have b0 : ∀ p : ℕ, (0 : ℝ) ≤ vV T'.V (p : T'.Fr) := fun p => by
      exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p
    have b1 : (vV T'.V (K : T'.Fr) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) +
        (Formalism.L2.Pj.DF Dw w : ℕ) * ((vV T'.V (α : T'.Fr) : ℝ) + vV T'.V (α' : T'.Fr)) +
        vV T'.V ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) := by
      rw [hK, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        vV_mul (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)))
          (Nat.cast_ne_zero.2 hc0),
        vV_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)),
        vV_pow (Nat.cast_ne_zero.2 hP0), vV_pow (Nat.cast_ne_zero.2 hM0)]
      conv_lhs => rw [show ((d.l₂.M : ℕ) : T'.Fr) = (α : T'.Fr) * (α' : T'.Fr) by rw [hα', Nat.cast_mul],
        vV_mul (Nat.cast_ne_zero.2 ha0) (Nat.cast_ne_zero.2 ha0')]
      push_cast
      ring
    have b2 : (vV T'.V (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E))) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * vV T'.V (α : T'.Fr) := by
      rw [nrm_nat, map_pow, map_natCast, vV_pow (Nat.cast_ne_zero.2 ha0)]
      push_cast
      ring
    have b3 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (Formalism.L2.Pj.DF Dw w : ℝ) / 2 ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) / (r * e : ℕ) := by
      have h := ram_sum_le_vV_discr D.host.E T' _ (fun p (hp : p ∈ D.host.condN.primeFactors) => Nat.prime_of_mem_primeFactors hp)
        (r * e) (Formalism.L2.Pj.DF Dw w)
      rw [← hP₀, Nat.cast_pow, vV_pow (Nat.cast_ne_zero.2 hP0), Int.cast_mul, Int.cast_natCast] at h
      rw [hP₀] at h ⊢
      exact h
    have b4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (α' : T'.Fr) : ℝ) / (r * e : ℕ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (b0 _)) heR.le
    rw [b1, b2, add_div, add_div, mul_add, add_div]
    linarith
  · congr 1
    simp only [map_mul, map_inv₀, map_natCast]
    field_simp

end GlobalTheory.CovInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationsAtAllPrimes
section
namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem hom_ext_of_localization_atPrime : ∀ (S : Type) [CommRing S] (W : Scheme.{0}) (z z' : Sp S ⟶ W),
    (∀ q : PrimeSpectrum S, spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z =
      spMap (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ z') → z = z' := by
  intro S _ W z z' h
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  let q : PrimeSpectrum S := x
  have e : (Sp S).fromSpecStalk q =
      Spec.map (Spec.stalkIso (CommRingCat.of S) q).inv ≫
        spMap (algebraMap S (Localization.AtPrime q.asIdeal)) := by
    rw [Spec.fromSpecStalk_eq, spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of S) (x := q)).symm
  change (Sp S).fromSpecStalk q ≫ z = (Sp S).fromSpecStalk q ≫ z'
  rw [e, Category.assoc, Category.assoc, h q]

end GlobalTheory.FlagMod.FieldFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupIClosedPointEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

namespace GlobalTheory.ZH.ThetaSys

theorem supI_closedPoint_eq : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω),
    M.HasDiv S.th → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z)
    (emb : Ω →+* FractionRing V), (∀ (U : M.Z.Opens) (f : Γ(M.Z, U)), ξ (IsLocalRing.closedPoint V) ∈ U →
      emb (valF M.pt U f) = algebraMap V (FractionRing V) (valR ξ U f)) →
    S.supI M (ξ (IsLocalRing.closedPoint V)) =
      {a | S.th a ≠ 0 ∧ ∀ b, ∃ v : V, emb (S.th b) = algebraMap V (FractionRing V) v * emb (S.th a)} := by
  intro o Ω _ _ _ S M hD V _ _ _ ξ emb hemb
  set z := ξ (IsLocalRing.closedPoint V) with hzdef
  have hs : ξ (IsLocalRing.closedPoint V) ⤳ z := specializes_rfl
  have key : ∀ (x : Ω) (hx : x ∈ M.O z), emb x = algebraMap V (FractionRing V) (RatModel.valLoc ξ z hs ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨U, f, hz, rfl⟩ := hx
    rw [RatModel.valLoc_valF ξ hs hz f]
    exact hemb U f hz
  ext a
  simp only [supI, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨ha, fun b => ⟨RatModel.valLoc ξ z hs ⟨_, hb b⟩, ?_⟩⟩
    rw [← key _ (hb b), ← map_mul, div_mul_cancel₀ _ ha]
  · rintro ⟨ha, hc⟩
    obtain ⟨x₀, hx₀⟩ := hD z
    obtain ⟨v, hv⟩ := hc x₀
    have hea : emb (S.th a) ≠ 0 := (map_ne_zero emb).2 ha
    have hw := key _ (hx₀.2 a)
    have hunit : IsUnit (RatModel.valLoc ξ z hs ⟨_, hx₀.2 a⟩) := by
      refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
      have hv0 : algebraMap V (FractionRing V) v ≠ 0 := by
        intro h0
        exact (map_ne_zero emb).2 hx₀.1 (by rw [hv, h0, zero_mul])
      rw [map_mul, map_one, ← hw, map_div₀, hv]
      field_simp
    have hu : IsUnit (⟨S.th a / S.th x₀, hx₀.2 a⟩ : M.O z) :=
      (RatModel.isUnit_valLoc_iff ξ hzdef.symm _).1 hunit
    exact (hx₀.div_iff_isUnit a).2 hu

end GlobalTheory.ZH.ThetaSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLettersIntegralLieBasisEigenframeRelationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_letters_integralLieBasis_eigenframe_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : GlobalTheory.LamT.LocMod z T iK),
    (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) →
    ∀ A : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) z.K, GlobalTheory.LamF.IsModelAt z.B.pol z.Φ.key z.m'.φ p A →
    letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
    ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
      (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
      φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
      GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
      ∃ (nu mu : Fin z.Φ.T.g → TanM yT.x Xo.univ.t.G) (C : (Σ b : E →+* ℂ, Fin (Dw.mult b)) → Fin z.Φ.T.g → T.Fr),
        (∀ σ k, C σ k ∈ Set.range (algebraMap T.V T.Fr)) ∧
        (∀ σ, fullB yT σ = ∑ k, iK (z.U (z.e σ) k) • nu k) ∧
        (∀ k, mu k = ∑ l, iK (A k l) • nu l) ∧
        ∀ b i, ∑ j, g b i j • fullB yT ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k := by
  first | exact @GlobalTheory.LamT.TanRel.tangent_letter_model_relation | exact GlobalTheory.LamT.TanRel.tangent_letter_model_relation | (intros; apply GlobalTheory.LamT.TanRel.tangent_letter_model_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfIntersectionNefLeCuspFormGrowthStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSelfIntersection_nef_le_cuspFormGrowth : GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (u : AllWt.Weight Dw), IsVariety₀ X Z → 1 ≤ dimFlag Dw → (∀ la, CuspIso X Z U la) → (∃ f : Cusp Z U u, f ≠ 0) → letI := algebraΓOfHom (str₀ X Z); IsNef c.F (L₀ X Z u) → ENNReal.ofReal (topSelfIntersection c.F (L₀ X Z u) (dimFlag Dw) : ℝ) ≤ GlobalTheory.CompHt.growthOn U Z (wtOf Dw u 0) := by
  first | exact @GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | exact GlobalTheory.NefCuspGrowth.topSelf_le_growthOn | (intros; apply GlobalTheory.NefCuspGrowth.topSelf_le_growthOn <;> assumption)
end

