module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinsMerge
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC _root_.Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def comap {Tp Tp' : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (f : Tp' → Tp) : OMDat C R i Tp' (fun t => tup (f t)) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := fun t => O.dδ (f t)
  Cl' := fun t => O.Cl' (f t)
  fCl := fun t => O.fCl (f t)
  bad := fun t => O.bad (f t)
  Lh := fun t => O.Lh (f t)
  La := fun t => O.La (f t)
  Nc := fun t => O.Nc (f t)
  gam := fun t => O.gam (f t)
  vol := fun t => O.vol (f t)
  ep := fun t => O.ep (f t)
  B := fun t => O.B (f t)
  epF := fun t => O.epF (f t)
  io := O.io
  hw := O.hw
  φ := fun t => O.φ (f t)
  w := fun t => O.w (f t)
  U₂ := fun t => O.U₂ (f t)
  dict₂ := fun t => O.dict₂ (f t)
  xi := fun t => O.xi (f t)
  thAd := fun t => O.thAd (f t)
  Plc := fun t => O.Plc (f t)

theorem pins_comap {Tp Tp' : Type} {tup : Tp → T0} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) : (comap O f).Pins κ v₀ ι x₀ :=
  ⟨h.lift, fun t => h.tuple (f t), h.act, fun t => h.bad (f t), fun t => h.reps (f t), fun t => h.ep (f t), h.io,
    fun t => h.w (f t), fun t => h.cov (f t), h.cxi.imp fun _ hc => ⟨hc.1, fun t => hc.2 (f t)⟩, fun t => h.model₂ (f t)⟩

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

def merge : OMDat C R i J tup where
  c' := c₃
  hle := h₃
  jL := jL₃
  hV := hV₃
  c0' := c0₃
  lev := lev
  dδ := fun j => covBC (hs j) ((src j).dδ ()) (u j)
  Cl' := fun j => (src j).Cl' ()
  fCl := fun j => (src j).fCl ()
  bad := fun j => (src j).bad ()
  Lh := fun j => (src j).Lh ()
  La := fun j => (src j).La ()
  Nc := fun j => (src j).Nc ()
  gam := fun j => (src j).gam ()
  vol := fun j => incF _ c₃ (hs j) ((src j).vol ())
  ep := fun j k => incF _ c₃ (hs j) ((src j).ep () k)
  B := fun j I => incF _ c₃ (hs j) ((src j).B () I)
  epF := fun j L => incF _ c₃ (hs j) ((src j).epF () L)
  io := io₃
  hw := hw₃
  φ := fun j x => incF _ c₃ (hs j) ((src j).φ () x)
  w := fun j k q => incF _ c₃ (hs j) ((src j).w () k q)
  U₂ := fun j => covUnf (hs j) ((src j).dδ ()) (u j) ((src j).U₂ ())
  dict₂ := fun j => (src j).dict₂ ()
  xi := fun j => (src j).xi ()
  thAd := fun j => thAdOf R i (tup j) (h j) c0₃ v₀
  Plc := fun j x => ∃ x₀, Place R i (tup j) (h j) c0₃ (jVx R i (tup j) x₀) x

theorem repsR_map {K K' : Type} [Field K] [Field K'] (j : K →+* K') {t : T0} {Cl : Type} {h : Cl → GA D (Vc D i)} {bad J' Lh gam}
    {vol : K} (hr : RepsR R i t h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam (j vol) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  exact ⟨h1, h2, h3, h4, by rw [h5, map_inv₀, map_natCast], h6⟩


end Merge

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PuncturedLineOpenCofinite
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem punctured_line_open_cofinite : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  intro k _ V hV χ₁ h₁
  classical

  have key : ∀ (χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k)
      (g : Localization.Away (Polynomial.X : Polynomial k)),
      g ∉ PrimeSpectrum.asIdeal (spMap χ.toRingHom (IsLocalRing.closedPoint k)) ↔ χ g ≠ 0 := by
    intro χ g
    rw [Spec.map_base]
    change g ∉ (PrimeSpectrum.comap χ.toRingHom (IsLocalRing.closedPoint k)).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hb : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    rw [hb, Ideal.mem_bot]
    rfl
  have hV' : IsOpen (V : Set (PrimeSpectrum (Localization.Away (Polynomial.X : Polynomial k)))) := hV
  obtain ⟨_, ⟨g, rfl⟩, hg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens).exists_subset_of_mem_open h₁ hV'
  have hg₁ : χ₁ g ≠ 0 := (key χ₁ g).1 hg
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (Polynomial.X : Polynomial k) g
  have hXu : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ Polynomial.X) ≠ 0 := fun χ =>
    ((IsLocalization.Away.algebraMap_isUnit (Polynomial.X : Polynomial k)).map χ).ne_zero
  have hev : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, ∀ q : Polynomial k,
      χ (algebraMap (Polynomial k) _ q) = q.eval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
    intro χ q
    have : χ.comp (IsScalarTower.toAlgHom k (Polynomial k) (Localization.Away (Polynomial.X : Polynomial k)))
        = Polynomial.aeval (χ (algebraMap (Polynomial k) _ Polynomial.X)) := by
      apply Polynomial.algHom_ext
      simp
    have h2 := congrArg (fun φ => φ q) this
    simpa [Polynomial.coe_aeval_eq_eval] using h2
  have hχp : ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k,
      χ (algebraMap (Polynomial k) _ p) = χ g * (χ (algebraMap (Polynomial k) _ Polynomial.X)) ^ n := by
    intro χ
    rw [← hp, map_mul, map_pow]
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hχp χ₁
    rw [map_zero, map_zero] at this
    exact mul_ne_zero hg₁ (pow_ne_zero _ (hXu χ₁)) this.symm
  refine (Polynomial.finite_setOf_isRoot hp0).subset ?_
  rintro c ⟨hc0, hcall⟩
  by_contra hroot
  have hunit : ∀ y : Submonoid.powers (Polynomial.X : Polynomial k),
      IsUnit (Polynomial.aeval c (y : Polynomial k)) := by
    rintro ⟨_, m, rfl⟩
    simp [hc0]
  let χc : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (Polynomial.X : Polynomial k)) hunit
  have hχc : χc (algebraMap (Polynomial k) _ Polynomial.X) = c := by
    simp [χc, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  apply hcall χc hχc
  apply hgV
  refine (key χc g).2 ?_
  intro h0
  apply hroot
  have := hχp χc
  rw [h0, zero_mul, hev, hχc] at this
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLineBundleSectionsLeImageForms
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry Filter GlobalTheory.Twist GlobalTheory.Points

namespace GlobalTheory.SecGrowth

section Ratio

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def ratioSub (ev : V →ₗ[K] Ω) : Subfield Ω where
  carrier := {r | ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    r * h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω)}
  mul_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show a * c * (h1 * h2) = (a * h1) * (c * h2) by ring]; exact Submodule.mul_mem_mul p1 p2
  one_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [one_mul, pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩
  add_mem' := by
    rintro a c ⟨e1, h1, m1, n1, p1⟩ ⟨e2, h2, m2, n2, p2⟩
    refine ⟨e1 + e2, h1 * h2, ?_, mul_ne_zero n1 n2, ?_⟩
    · rw [pow_add]; exact Submodule.mul_mem_mul m1 m2
    · rw [pow_add, show (a + c) * (h1 * h2) = (a * h1) * h2 + h1 * (c * h2) by ring]
      exact add_mem (Submodule.mul_mem_mul p1 m2) (Submodule.mul_mem_mul m1 p2)
  zero_mem' := ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [zero_mul]; exact zero_mem _⟩
  neg_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    exact ⟨e, h, m, n, by rw [neg_mul]; exact neg_mem p⟩
  inv_mem' := by
    rintro a ⟨e, h, m, n, p⟩
    by_cases ha : a = 0
    · refine ⟨e, h, m, n, ?_⟩
      rw [ha, inv_zero, zero_mul]; exact zero_mem _
    · exact ⟨e, a * h, p, mul_ne_zero ha n, by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]; exact m⟩

theorem algebraMap_mem_ratioSub (ev : V →ₗ[K] Ω) (c : K) : algebraMap K Ω c ∈ ratioSub ev :=
  ⟨0, 1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero,
    by rw [mul_one, pow_zero]; exact Submodule.mem_one.2 ⟨c, rfl⟩⟩

theorem div_mem_ratioSub (ev : V →ₗ[K] Ω) (v w : V) : ev v / ev w ∈ ratioSub ev := by
  by_cases hw : ev w = 0
  · rw [hw, div_zero]; exact zero_mem _
  · refine ⟨1, ev w, by rw [pow_one]; exact LinearMap.mem_range_self ev w, hw, ?_⟩
    rw [div_mul_cancel₀ _ hw, pow_one]; exact LinearMap.mem_range_self ev v

theorem isRatio_of_mem {ev : V →ₗ[K] Ω} {τ : ℕ} {t w : Ω} (hw : w ∈ LinearMap.range ev) (hw0 : w ≠ 0)
    (ht : t / w ^ τ ∈ ratioSub ev) : DegCmp.IsRatio ev τ t := by
  obtain ⟨e, h, m, n, p⟩ := ht
  refine ⟨e, h, m, n, ?_⟩
  have : t * h = w ^ τ * (t / w ^ τ * h) := by field_simp
  rw [this, pow_add]
  exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ hw τ) p

end Ratio

section Integral

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

theorem eval₂_mem_coneAlg (ev : V →ₗ[K] Ω) {r : ℕ} (v : Fin r → V) (g : MvPolynomial (Fin r) K) :
    eval₂ (Polynomial.C.comp (algebraMap K Ω)) (fun i => Polynomial.C (ev (v i)) * Polynomial.X) g ∈
      DegCmp.coneAlg ev := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [eval₂_C, RingHom.comp_apply, ← Polynomial.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p i hp =>
    rw [eval₂_mul, eval₂_X]
    refine mul_mem hp ?_
    rw [mul_comm]
    exact Algebra.subset_adjoin ⟨v i, rfl⟩

theorem isIntDeg_of_eq {ev : V →ₗ[K] Ω} {r : ℕ} (v : Fin r → V) {τ : ℕ} {t : Ω} {n : ℕ}
    (c : Fin n → MvPolynomial (Fin r) K)
    (h : (Polynomial.C t * Polynomial.X ^ τ) ^ n + ∑ k, eval₂ (Polynomial.C.comp (algebraMap K Ω))
      (fun i => Polynomial.C (ev (v i)) * Polynomial.X) (c k) * (Polynomial.C t * Polynomial.X ^ τ) ^ (k : ℕ) = 0) :
    DegCmp.IsIntDeg ev τ t := by
  let c' : Fin n → DegCmp.coneAlg ev := fun k => ⟨_, eval₂_mem_coneAlg ev v (c k)⟩
  refine ⟨Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (c' k) * Polynomial.X ^ (k : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt c'), ?_⟩
  rw [mul_comm (Polynomial.X ^ τ)]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow]
  exact h

end Integral

variable {k : Type} [Field k] (S : LinSys k)

theorem comb_single (i : Fin S.N) : S.comb (Pi.single i 1) = S.b i := by
  rw [LinSys.comb, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_smul])
    (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, map_one, one_smul]

theorem sec_eq_zero_of_generic [IsReduced S.Y] {η : S.Y} (hη : IsGenericPoint η Set.univ) {m : ℤ}
    (s : (lbZPow S.L m).Sec) (h : η ∉ nonzeroLocus s) : s = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy.2⟩)).elim

theorem growth_mono (D : ℕ) {r r' : ℕ → ℕ∞} (h : ∀ τ, r τ ≤ r' τ) : growth D r ≤ growth D r' :=
  limsup_le_limsup (Eventually.of_forall fun τ => by
    gcongr
    exact h τ)

theorem finrank_le_toENat (R M : Type) [Field R] [AddCommGroup M] [Module R M] :
    (Module.finrank R M : ℕ∞) ≤ Cardinal.toENat (Module.rank R M) := by
  by_cases h : Module.Finite R M
  · rw [← Module.finrank_eq_rank]; simp
  · rw [Module.finrank_of_not_finite h]; simp

def powValLin {Ω : Type} [Field Ω] [Algebra k Ω] (x : S.Pt Ω) (m : ℕ) :
    letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
    (lbPow S.L m).Sec →ₗ[k] Ω :=
  letI : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  { toFun := fun s => S.powVal (m := (m : ℤ)) x.1 s
    map_add' := fun s t => by
      change S.powVal x.1 (s + t) = S.powVal x.1 s + S.powVal x.1 t
      rw [LinSys.powVal, LinSys.powVal, LinSys.powVal, zfun_add]
      exact valR_add x.1 _ (S.le_chartAt x.1) _ _
    map_smul' := fun c s => by
      rw [RingHom.id_apply, Algebra.smul_def]
      have e : c • s = algebraMap k Γ(S.Y, ⊤) c • s := rfl
      change S.powVal x.1 (c • s) = _
      rw [e]
      rw [LinSys.powVal, LinSys.powVal, zfun_smul]
      exact (valR_mul x.1 _ (S.le_chartAt x.1) _ _).trans (congrArg (· * _)
        ((valR_res x.1 le_top (S.le_chartAt x.1) _).trans ((S.valR_algebraMap x.1 c).trans
          (congrFun (congrArg DFunLike.coe (LinSys.baseHom_ptOver x)) c)))) }

theorem rankGrowth_lineBundleSections_le_image_forms : ∀ (k : Type) [Field k] [CharZero k] (S : LinSys k), S.IsVariety → S.BasePointFree →
    S.Birational → growth S.D (fun m => (lbH0 k (lbPow S.L m) : ℕ∞)) ≤
      growth S.D (fun m => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) := by
  intro k _ _ S hS hb hbir
  obtain ⟨η, hη, hrat⟩ := hbir
  have : IsIntegral S.Y := HeightExists.isIntegral hS
  letI : Algebra k (S.Y.residueField η) := (S.baseHom (resPt η)).toAlgebra
  let x : S.Pt (S.Y.residueField η) := ⟨resPt η, S.comp_str _⟩
  have hx : IsGenericPoint (ptOf x.1) Set.univ := by rw [ptOf_resPt]; exact hη
  let b := Pi.basisFun k (Fin S.N)
  let ev := b.constr k (S.coords (resPt η))
  have hev : ∀ j, ev (b j) = S.coords (resPt η) j := fun j => b.constr_basis k _ j
  have hI : S.imageIdeal = imageIdeal ev b := by
    rw [imageIdeal_eq_coneIdeal_of_generic k _ S x hx 1 (S.coords (resPt η)) one_ne_zero (one_smul _ _).symm,
      CompHt.imageIdeal]
    exact congrArg _ (funext fun j => (hev j).symm)
  have hR : (fun m : ℕ => (Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) : ℕ∞)) =
      fun m => DegCmp.hilb ev (1 * m) := by
    funext m
    rw [one_mul, hI, DegCmp.hilb_eq_finrank_quotPiece k _ _ ev S.N b m]
  rw [hR]
  letI (m : ℕ) : Module k (lbPow S.L m).Sec := Module.compHom _ (algebraMap k Γ(S.Y, ⊤))
  haveI (m : ℕ) : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec := IsScalarTower.of_compHom _ _ _
  have hinj : ∀ m, Function.Injective (powValLin S x m) := fun m => by
    refine (injective_iff_map_eq_zero _).2 fun s hs => sec_eq_zero_of_generic S hη (m := (m : ℤ)) s fun hm => ?_
    rw [← ptOf_resPt η] at hm
    exact (S.powVal_ne_zero_iff (resPt η) s).2 hm hs
  refine le_trans (growth_mono S.D fun m => ?_)
    (ConeDeg.growth_rank_le ev S.D 1 le_rfl (fun m => LinearMap.range (powValLin S x m)) ?_)
  · rw [rank_range_of_injective _ (hinj m), lineBundleGlobalSectionsDim_eq_finrank]
    exact finrank_le_toENat _ _
  · intro m t ht
    obtain ⟨s, rfl⟩ := ht
    rw [one_mul]
    obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero (resPt η))
    have hyj : S.coords (resPt η) j ≠ 0 := hj
    refine ⟨?_, ?_⟩
    · obtain ⟨n, c, hc⟩ := isIntegral_coneRing_of_forall_valuationSubring k (S.Y.residueField η) (algebraMap k _)
        S.N m (S.coords (resPt η)) (powValLin S x m s) fun V hV => by
          obtain ⟨i, hi, hV'⟩ := LinSys.exists_ratio_mem_of_point S hS S.N m (fun i => Pi.single i 1) s
            (fun y => by
              obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hb.ge (Set.mem_univ y))
              exact ⟨i, by rw [comb_single]; exact hi⟩) (resPt η) V hV
          have e : S.val (resPt η) (S.comb (Pi.single i 1)) = S.coords (resPt η) i := by rw [comb_single]; rfl
          rw [e] at hi hV'
          exact ⟨i, hi, hV'⟩
      exact isIntDeg_of_eq b c (by simpa only [hev] using hc)
    · refine isRatio_of_mem ⟨b j, hev j⟩ hyj ?_
      have hle : S.ratioField (resPt η) ≤ ratioSub ev := Subfield.closure_le.2 (Set.union_subset
        (by rintro _ ⟨c, rfl⟩; exact algebraMap_mem_ratioSub ev c)
        (by rintro _ ⟨i, i', rfl⟩; rw [← hev i, ← hev i']; exact div_mem_ratioSub ev _ _))
      exact hle (hrat ▸ Subfield.mem_top _)

end GlobalTheory.SecGrowth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelDimLeOfIsClosedImmersion
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_le_of_formallyUnramified (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Nontrivial C]
    [Algebra.FormallyUnramified B C] (g g' : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g R B]
    [Algebra.IsStandardSmoothOfRelativeDimension g' R C] : g' ≤ g := by
  have : Nontrivial B := (algebraMap B C).domain_nontrivial
  have : Algebra.IsStandardSmooth R B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Module.Free B Ω[B⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange R B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map R B C x).mp (Subsingleton.elim _ _)
  have h1 := LinearMap.rank_le_of_surjective _ hs
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g', Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g] at h1
  simpa using h1

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_surjective_away {R B A L : Type} [CommRing R] [CommRing B] [CommRing A] [CommRing L]
    [Algebra A L] (t : A) [IsLocalization.Away t L] [Nontrivial L] (φ : R →+* B) (ψ : B →+* A)
    (hψ : Function.Surjective ψ) (g g' : ℕ) (hφ : RingHom.IsStandardSmoothOfRelativeDimension g φ)
    (hL : RingHom.IsStandardSmoothOfRelativeDimension g' ((algebraMap A L).comp (ψ.comp φ))) :
    g' ≤ g := by
  letI : Algebra R B := φ.toAlgebra
  letI : Algebra B A := ψ.toAlgebra
  letI : Algebra B L := ((algebraMap A L).comp ψ).toAlgebra
  letI : Algebra R L := ((algebraMap A L).comp (ψ.comp φ)).toAlgebra
  haveI : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyUnramified B A := Algebra.FormallyUnramified.of_surjective (Algebra.ofId B A) hψ
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyUnramified B L := Algebra.FormallyUnramified.comp B A L
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g' R L := hL
  exact relDim_le_of_formallyUnramified R B L g g'

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G),
    IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  intro k _ N G ν hν ⟨x⟩ g g' hG hN
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hG.exists_isStandardSmoothOfRelativeDimension (ν.left x)
  let V' : N.left.Opens := ν.left ⁻¹ᵁ V
  have hV' : IsAffineOpen V' := hV.preimage ν.left
  have hN' : SmoothOfRelativeDimension g' (ν.left ≫ G.hom) := by rw [Over.w ν]; exact hN
  have e' : V' ≤ (ν.left ≫ G.hom) ⁻¹ᵁ U := fun y hy => e hy
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g') _ hN' ⟨U, hU⟩ ⟨V', hV'⟩ e'
  have : Nonempty V' := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(N.left, V')
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1
      (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have hψ : Function.Surjective (ν.left.appLE V V' le_rfl).hom := by
    have := ν.left.app_surjective V hV
    rw [Scheme.Hom.app_eq_appLE] at this
    exact this
  refine relDim_le_of_surjective_away (L := Localization.Away t) t (G.hom.appLE U V e).hom
    (ν.left.appLE V V' le_rfl).hom hψ g g' h ?_
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE ν.left G.hom U V V' e le_rfl]
  exact h₁

end GlobalTheory
end

