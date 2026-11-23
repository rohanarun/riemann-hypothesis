module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Flat

variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ U) (u : Γ(X, U)ˣ) :
    res h1 (res h2 u) = res (h1.trans h2) u := by
  apply Units.ext
  show (X.presheaf.map (homOfLE h1).op).hom ((X.presheaf.map (homOfLE h2).op).hom (u : Γ(X, U))) =
    (X.presheaf.map ((homOfLE h2).op ≫ (homOfLE h1).op)).hom (u : Γ(X, U))
  rw [Functor.map_comp]
  rfl

lemma flat_le {K : Type} [Fintype K] (p : (K → L₁.ι) × (K → L₂.ι)) (k : K) :
    LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 ≤
      (L₂.pull f₂).U (fun _ => p.2 k) ⊓ (L₁.pull f₁).U (fun _ => p.1 k) := by
  intro x hx
  simp only [LB.pull, LB.LinComb, LB.wchart, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_mk,
    Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hx ⊢
  exact ⟨fun _ => hx.2 k, fun _ => hx.1 k⟩

def flatIso (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) {K : Type} [Fintype K] (ε : K → ℤ) :
    LB.Iso (LB.LinComb L₂ (fun _ : K => f₂) ε) (LB.LinComb L₁ (fun _ : K => f₁) ε) :=
  ⟨fun p => ∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k)⟩


lemma comm_alg {M : Type*} [CommGroup M] (a b c : M) (n : ℤ) :
    (a * b⁻¹ * c) ^ (-n) = b ^ n * (a ^ n)⁻¹ * c ^ (-n) := by
  rw [mul_zpow, mul_zpow, zpow_neg a, inv_zpow', neg_neg, mul_comm ((a ^ n)⁻¹) (b ^ n)]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
lemma gm_pull_g' {Z : Scheme.{0}} {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (a b : L.ι)
    (ha : f (r z) ∈ L.U a) (hb : f (r z) ∈ L.U b) :
    gm r z ((L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) ((L.pull f).g (fun _ => a) (fun _ => b)) =
      gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) := by
  exact (gm_linComb L (fun _ : PUnit => f) (fun _ => 1) r z (fun _ => a) (fun _ => b)
    (Set.mem_iInter.2 fun _ => ha) (Set.mem_iInter.2 fun _ => hb)).trans (by simp)

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
set_option maxHeartbeats 1000000 in
theorem flatIso_isGen (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) {K : Type} [Fintype K] (ε : K → ℤ) :
    (flatIso L₁ L₂ f₁ f₂ w ε).IsGen := by
  have hP := (isGen_iff w).1 hw
  intro (p : (K → L₁.ι) × (K → L₂.ι)) (q : (K → L₁.ι) × (K → L₂.ι))
  apply unit_ext
  intro y hy
  have hp : y ∈ LB.wchart L₁ (fun _ : K => f₁) p.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) p.2 := hy.1
  have hq : y ∈ LB.wchart L₁ (fun _ : K => f₁) q.1 ⊓ LB.wchart L₂ (fun _ : K => f₂) q.2 := hy.2
  show gm (𝟙 Y) y _ (res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ p k) (w.s (fun _ => p.2 k, fun _ => p.1 k)) ^ (-ε k))) =
    gm (𝟙 Y) y _ ((res _ ((LB.LinComb L₁ (fun _ : K => f₁) ε).g p.1 q.1) *
      (res _ ((LB.LinComb L₂ (fun _ : K => f₂) ε).g p.2 q.2))⁻¹) *
      res _ (∏ k, res (flat_le L₁ L₂ f₁ f₂ q k) (w.s (fun _ => q.2 k, fun _ => q.1 k)) ^ (-ε k)))
  erw [map_mul, map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy,
    gm_linComb L₁ _ ε (𝟙 Y) y p.1 q.1 hp.1 hq.1, gm_linComb L₂ _ ε (𝟙 Y) y p.2 q.2 hp.2 hq.2]
  erw [map_prod, map_prod]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h1 : f₁ y ∈ L₁.U (p.1 k) := Set.mem_iInter.1 hp.1 k
  have h1' : f₁ y ∈ L₁.U (q.1 k) := Set.mem_iInter.1 hq.1 k
  have h2 : f₂ y ∈ L₂.U (p.2 k) := Set.mem_iInter.1 hp.2 k
  have h2' : f₂ y ∈ L₂.U (q.2 k) := Set.mem_iInter.1 hq.2 k
  have e := hP Y (𝟙 Y) y (p.2 k) (q.2 k) (fun _ => p.1 k) (fun _ => q.1 k) (by simpa using h2) (by simpa using h2')
    (Set.mem_iInter.2 fun _ => by simpa using h1) (Set.mem_iInter.2 fun _ => by simpa using h1')
  rw [gm_pull_g' L₁ f₁ (𝟙 Y) y (p.1 k) (q.1 k) (by simpa using h1) (by simpa using h1')] at e
  rw [map_zpow, map_zpow]
  erw [gm_res _ y _ hp, gm_res _ y _ hq]
  change _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y) y (p.2 k) (fun _ => p.1 k) ^ (-ε k) = _ * _ * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.gw w (𝟙 Y) y (q.2 k) (fun _ => q.1 k) ^ (-ε k)
  rw [e]
  simp only [Category.id_comp]
  exact comm_alg _ _ _ _

end Flat

section NZ

variable {Y : Scheme.{0}}

lemma mem_nonzeroLocus {M : LB Y} (s : LB.Sec M) (y : Y) :
    y ∈ nonzeroLocus s ↔ ∃ j, y ∈ Y.basicOpen (s.f j) := by
  rw [nonzeroLocus, TopologicalSpace.Opens.mem_iSup]

theorem nonzeroLocus_secOfIso {A B : LB Y} (u : LB.Iso A B) (t : LB.Sec B) (hu : u.IsGen) (hA : A.IsLB)
    (hB : B.IsLB) : nonzeroLocus t ≤ nonzeroLocus (secOfIso (u := u) t hu hA hB) := by
  intro y hy
  obtain ⟨b, hb⟩ := (mem_nonzeroLocus t y).1 hy
  have hyb : y ∈ B.U b := Y.basicOpen_le _ hb
  obtain ⟨a, ha⟩ : ∃ a, y ∈ A.U a := by
    have : y ∈ (⨆ a, A.U a : Y.Opens) := by rw [hA.cover]; trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  refine (mem_nonzeroLocus _ y).2 ⟨a, ?_⟩
  have e := secOfIso_spec (u := u) t hu hA hB a b
  have e2 := congrArg Y.basicOpen e
  rw [isoCand, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _), Scheme.basicOpen_res,
    Scheme.basicOpen_res] at e2
  have hmem : y ∈ (A.U a ⊓ B.U b) ⊓ ((A.U a ⊓ B.U b) ⊓ Y.basicOpen (t.f b)) := ⟨⟨ha, hyb⟩, ⟨ha, hyb⟩, hb⟩
  rw [← e2] at hmem
  exact hmem.2

end NZ

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end Main

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullExp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

abbrev gK : pullback G.hom (jK V) ⟶ G.left := pullback.fst G.hom (jK V)

def endK (f : G ⟶ G) : pullback G.hom (jK V) ⟶ pullback G.hom (jK V) :=
  pullback.map G.hom (jK V) G.hom (jK V) f.left (𝟙 _) (𝟙 _) (by simp) (by simp)

def unitK : Spec (CommRingCat.of (FractionRing V)) ⟶ pullback G.hom (jK V) :=
  pullback.lift (jK V ≫ eSec G) (𝟙 _) (by simp [eSec])

def IsPullByEnd (U : Unif (maximalIdeal V) D A G) (f : G ⟶ G) (k N : ℕ) (s : U.SecK k) (s' : U.SecK (k * N)) : Prop :=
  ∃ u : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)]), u.IsGen ∧
    LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ u unitK)
      (LB.pullGen U.LG.L _ _ (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig (k * (N - 1))) (jK V)) ∧
    GeneratorPullback.SecRel U.LG.L (fun _ : Fin 1 => gK) (fun _ => ((k * N : ℕ) : ℤ)) s'
      (fun _ : Fin 1 => gK) (fun _ => (k : ℤ)) s (endK f)
      ![gK, endK f ≫ gK] ![((k * N : ℕ) : ℤ), -(k : ℤ)] u

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenVal
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

lemma hasVal_mul {c d : FractionRing V} {n m : ℤ} (hc : HasVal ϖ c n) (hd : HasVal ϖ d m) (hϖ : Irreducible ϖ) :
    HasVal ϖ (c * d) (n + m) := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨w, hw⟩ := hd
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  refine ⟨u * w, ?_⟩
  rw [hu, hw, zpow_add₀ hπ, Units.val_mul, map_mul]
  ring


open scoped Classical in
def valE (hϖ : Irreducible ϖ) (c : FractionRing V) : ℤ :=
  if h : c = 0 then 0 else (hasVal_of_ne_zero hϖ h).choose

lemma hasVal_valE (hϖ : Irreducible ϖ) {c : FractionRing V} (hc : c ≠ 0) : HasVal ϖ c (valE hϖ c) := by
  unfold valE
  rw [dite_eq_right hc]
  exact (hasVal_of_ne_zero hϖ hc).choose_spec


open scoped Classical in
def vK (hϖ : Irreducible ϖ) : AddValuation (FractionRing V) (WithTop ℚ) :=
  AddValuation.of (fun c => if c = 0 then ⊤ else ((valE hϖ c : ℚ) : WithTop ℚ))
    (by simp)
    (by
      have h1 : HasVal ϖ (1 : FractionRing V) 0 := ⟨1, by simp⟩
      simp [hasVal_unique hϖ (hasVal_valE hϖ one_ne_zero) h1])
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
      have key : ∀ {a b : FractionRing V}, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → valE hϖ a ≤ valE hϖ b →
          valE hϖ a ≤ valE hϖ (a + b) := by
        intro a b ha hb hab hle
        have hva := hasVal_valE hϖ ha
        have hvb := hasVal_valE hϖ hb
        have hvab := hasVal_valE hϖ hab
        generalize valE hϖ a = na at hva hle ⊢
        generalize valE hϖ b = nb at hvb hle
        generalize valE hϖ (a + b) = nab at hvab ⊢
        obtain ⟨u, hu⟩ := hva
        obtain ⟨w, hw⟩ := hvb
        obtain ⟨d, hd⟩ : ∃ d : ℕ, nb = na + d := ⟨(nb - na).toNat, by omega⟩
        set r : V := (u : V) + ϖ ^ d * (w : V)
        have hab' : a + b = algebraMap V (FractionRing V) ϖ ^ na * algebraMap V (FractionRing V) r := by
          rw [hu, hw, hd, zpow_add₀ hπ, zpow_natCast]
          simp only [r, map_add (f := _), map_mul, map_pow]
          ring
        have hr : r ≠ 0 := by
          rintro h0
          apply hab
          rw [hab', h0, map_zero, mul_zero]
        obtain ⟨k, z, hz⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
        have hv : HasVal ϖ (a + b) (na + k) :=
          ⟨z, by rw [hab', hz, zpow_add₀ hπ, zpow_natCast, map_mul, map_pow]; ring⟩
        rw [hasVal_unique hϖ hvab hv]
        omega
      rcases le_total (valE hϖ x) (valE hϖ y) with h | h
      · have := key hx hy hxy h
        exact min_le_of_left_le (by exact_mod_cast this)
      · have := key hy hx (by rwa [add_comm]) h
        rw [add_comm] at this
        exact min_le_of_right_le (by exact_mod_cast this))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      simp only [hx, hy, hxy, if_false]
      rw [hasVal_unique hϖ (hasVal_valE hϖ hxy) (hasVal_mul (hasVal_valE hϖ hx) (hasVal_valE hϖ hy) hϖ)]
      push_cast
      rfl)

lemma valOver_vK (hϖ : Irreducible ϖ) : ValOver ϖ (FractionRing V) (vK hϖ) := by
  intro c n hc
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  have hc0 : c ≠ 0 := by
    obtain ⟨u, hu⟩ := hc
    rw [hu]
    refine mul_ne_zero (zpow_ne_zero _ hπ) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr u.ne_zero
  change vK hϖ c = _
  simp only [vK, AddValuation.of_apply, if_neg hc0]
  rw [hasVal_unique hϖ (hasVal_valE hϖ hc0) hc]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValExt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem exists_valOver {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F] [Algebra (FractionRing V) F]
    [Algebra.IsAlgebraic (FractionRing V) F] : ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by
  classical
  let i : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V _)
  have ii : Function.Injective i := (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  obtain ⟨A, hA, hl⟩ := IsLocalRing.exists_factor_valuationRing i
  let w := A.valuation
  have le : ∀ r, w (i r) ≤ 1 := fun r => (A.valuation_le_one_iff _).2 (hA r)
  have un : ∀ u : Vˣ, w (i u) = 1 := fun u => le_antisymm (le _) (by
    have := le (↑u⁻¹ : V)
    have e : w (i u) * w (i ↑u⁻¹) = 1 := by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    calc 1 = w (i u) * w (i ↑u⁻¹) := e.symm
      _ ≤ w (i u) * 1 := mul_le_mul_right this _
      _ = _ := mul_one _)
  set p := w (i ϖ) with hp
  have p0 : 0 < p := zero_lt_iff.2 ((Valuation.ne_zero_iff w).2 fun h => hϖ.ne_zero (ii (h.trans (map_zero i).symm)))
  have p1 : p < 1 := lt_of_le_of_ne (le ϖ) fun h => hϖ.not_isUnit
    ((isUnit_map_iff (i.codRestrict A.toSubring hA) ϖ).1 ((A.valuation_eq_one_iff ⟨_, hA ϖ⟩).2 h))
  have hv : ∀ c n, HasVal ϖ c n → w (algebraMap _ F c) = p ^ n := by
    rintro _ n ⟨u, rfl⟩
    rw [map_mul, map_zpow₀, map_mul, map_zpow₀]
    exact (congrArg _ (un u)).trans (mul_one _)
  have ex : ∀ c : FractionRing V, c ≠ 0 → ∃ n : ℤ, w (algebraMap _ F c) = p ^ n := fun c hc => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) c
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (x := a) (by rintro rfl; simp at hc) hϖ
    obtain ⟨n, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
    refine ⟨m - n, ?_⟩
    rw [map_div₀, map_div₀, zpow_sub₀ p0.ne', zpow_natCast, zpow_natCast]
    show w (i _) / w (i _) = _
    simp only [map_mul, map_pow, un, one_mul, ← hp]
  have rat : ∀ x : F, x ≠ 0 → ∃ (n : ℕ) (m : ℤ), 0 < n ∧ w x ^ n = p ^ m := fun x hx => by
    by_contra hc
    push Not at hc
    obtain ⟨f, hf, h0⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing V) x
    let T := fun j => algebraMap _ F (f.coeff j) * x ^ j
    have wx : w x ≠ 0 := (Valuation.ne_zero_iff w).2 hx
    have ne : ∀ a ∈ f.support, ∀ b ∈ f.support, a < b → w (T a) ≠ w (T b) := fun a ha b hb hab h => by
      obtain ⟨r, hr⟩ := ex _ (Polynomial.mem_support_iff.1 ha)
      obtain ⟨s, hs⟩ := ex _ (Polynomial.mem_support_iff.1 hb)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
      simp only [T, map_mul, map_pow, hr, hs] at h
      rw [add_assoc, pow_add, mul_comm (w x ^ a), ← mul_assoc] at h
      refine hc (d + 1) (r - s) d.succ_pos ?_
      rw [zpow_sub₀ p0.ne', mul_right_cancel₀ (pow_ne_zero a wx) h, mul_div_cancel_left₀ _ (zpow_ne_zero s p0.ne')]
    obtain ⟨j, hj, hm⟩ := f.support.exists_max_image (fun j => w (T j)) (Polynomial.support_nonempty.2 hf)
    have := w.map_sum_eq_of_lt hj fun a ha => lt_of_le_of_ne (hm a (Finset.mem_sdiff.1 ha).1) (by
      rcases lt_or_gt_of_ne (Finset.notMem_singleton.1 (Finset.mem_sdiff.1 ha).2) with h | h
      exacts [ne a (Finset.mem_sdiff.1 ha).1 j hj h, (ne j hj a (Finset.mem_sdiff.1 ha).1 h).symm])
    rw [show ∑ a ∈ f.support, T a = 0 by rw [← h0, Polynomial.aeval_def, Polynomial.eval₂_eq_sum]; rfl, map_zero] at this
    exact mul_ne_zero ((map_ne_zero _).2 (Polynomial.mem_support_iff.1 hj)) (pow_ne_zero j hx) ((Valuation.zero_iff w).1 this.symm)
  have cmp : ∀ {x y : F} {n n' : ℕ} {m m' : ℤ}, 0 < n → 0 < n' → w x ^ n = p ^ m → w y ^ n' = p ^ m' →
      (w x ≤ w y ↔ (m' : ℚ) / n' ≤ m / n) := fun {x y n n' m m'} hn hn' h h' => by
    rw [← pow_le_pow_iff_left₀ zero_le zero_le (Nat.mul_pos hn hn').ne', pow_mul, h, mul_comm n, pow_mul, h', ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, zpow_le_zpow_iff_right_of_lt_one₀ p0 p1,
      div_le_div_iff₀ (by exact_mod_cast hn') (by exact_mod_cast hn)]
    exact_mod_cast Iff.rfl
  choose! N M hN hM using rat
  let v : F → WithTop ℚ := fun x => if x = 0 then ⊤ else ((M x : ℚ) / N x : ℚ)
  have spec : ∀ {x : F} {n : ℕ} {m : ℤ}, x ≠ 0 → 0 < n → w x ^ n = p ^ m → v x = ((m : ℚ) / (n : ℕ) : ℚ) := fun {x n m} hx hn h =>
    (if_neg hx).trans (congrArg _ (le_antisymm ((cmp hn (hN x hx) h (hM x hx)).1 le_rfl) ((cmp (hN x hx) hn (hM x hx) h).1 le_rfl)))
  have mono : ∀ x y, w x ≤ w y → v y ≤ v x := fun x y h => by
    by_cases hx : x = 0
    · simp [v, hx]
    · have hy : y ≠ 0 := by rintro rfl; exact hx ((Valuation.zero_iff w).1 (le_zero_iff.1 (h.trans_eq (map_zero w))))
      simp only [v, if_neg hx, if_neg hy, WithTop.coe_le_coe]
      exact (cmp (hN x hx) (hN y hy) (hM x hx) (hM y hy)).1 h
  refine ⟨AddValuation.of v (if_pos rfl) (by simpa using spec (n := 1) (m := 0) one_ne_zero one_pos (by simp)) (fun x y => ?_)
    fun x y => ?_, fun c n h => ?_⟩
  · rcases le_max_iff.1 (w.map_add x y) with h | h
    exacts [(min_le_left _ _).trans (mono _ _ h), (min_le_right _ _).trans (mono _ _ h)]
  · by_cases hx : x = 0
    · simp [v, hx]
    by_cases hy : y = 0
    · simp [v, hy]
    rw [spec (n := N x * N y) (m := M x * N y + M y * N x) (mul_ne_zero hx hy) (Nat.mul_pos (hN x hx) (hN y hy)) (by
      rw [map_mul, mul_pow, pow_mul, hM x hx, mul_comm (N x), pow_mul, hM y hy, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
        zpow_add₀ p0.ne'])]
    simp only [v, if_neg hx, if_neg hy, ← WithTop.coe_add, WithTop.coe_inj]
    have := (hN x hx).ne'
    have := (hN y hy).ne'
    push_cast
    field_simp
  · have e := hv c n h
    have := spec (n := 1) (m := n) ((Valuation.ne_zero_iff w).1 (e ▸ zpow_ne_zero n p0.ne')) one_pos ((pow_one _).trans e)
    simpa using this

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

