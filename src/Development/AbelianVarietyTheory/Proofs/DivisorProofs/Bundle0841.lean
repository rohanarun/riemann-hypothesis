module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocBasis

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def vec {S : Type} [CommRing S] (x : Sp S ⟶ X) {n : ℕ}
    (xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G)
    (cc : Fin n → S) : Sp (DualNumber S) ⟶ t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst t.G.hom x

section V

variable {t} {S : Type} [CommRing S] {x : Sp S ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G}

theorem push_ext {Y : Over (Spec (CommRingCat.of S))} {v v' : Y ⟶ (Over.pullback x).obj t.G}
    (h : v.left ≫ pullback.fst t.G.hom x = v'.left ≫ pullback.fst t.G.hom x) : v = v' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w v).trans (Over.w v').symm

theorem tan_iff (v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v.left ≫ pullback.fst t.G.hom x = (1 : Over.mk x ⟶ t.G).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by
  have hid : (sp (R₀ := S) S).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap S S)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e0 : (1 : sp (R₀ := S) S ⟶ (Over.pullback x).obj t.G).left ≫ pullback.fst t.G.hom x =
      (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left :=
    congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) S)))
  have e1 : (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left = (1 : Over.mk x ⟶ t.G).left := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    show ((sp (R₀ := S) S).hom ≫ x) ≫ _ = x ≫ _
    rw [hid, Category.id_comp]
  rw [← e1, ← e0, ← Category.assoc]
  constructor
  · intro e
    exact push_ext e
  · intro e
    exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem vec_tan (hx : IsUnivChart _ n xc) (cc : Fin n → S) : IsTanAtG t x (vec t x xc cc) := by
  refine ⟨?_, (tan_iff _).mpr (ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc)⟩
  show ((tvec (x := xc) cc).left ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Over.w (tvec (x := xc) cc))

theorem vec_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber S) ⟶ t.G.left) (hw : IsTanAtG t x w) :
    ∃ cc, w = vec t x xc cc := by
  let v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G :=
    Over.homMk (pullback.lift w _ hw.1) (pullback.lift_snd _ _ _)
  have hv : v.left ≫ pullback.fst t.G.hom x = w := pullback.lift_fst _ _ _
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := (tan_iff v).mp (by rw [hv]; exact hw.2)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht, ?_⟩
  have e : v = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht) := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v ht
  rw [← hv]
  exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → S) (e : Fin m → Fin n → S) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → S) 0
    rw [add_zero] at h
    simpa using mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      ih (fun j => a j.succ) (fun j => e j.succ), List.ofFn_succ, List.prod_cons]

theorem comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → S) (a : Fin m → S) (cc : Fin n → S) :
    IsCombAtG t x (fun j => vec t x xc (e j)) a (vec t x xc cc) ↔ cc = ∑ j, a j • e j := by
  let P := pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) (DualNumber S))
  let W' : Fin m → (tEpsG x ⟶ t.G) := fun j =>
    P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
  have hW' : ∀ j, (W' j).left = spMap (epsMul (a j)) ≫ vec t x xc (e j) := fun j =>
    Category.assoc _ _ _
  have hP : ((List.ofFn W').prod).left = vec t x xc (∑ j, a j • e j) := by
    have h := map_list_prod P
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
    rw [← tvec_sum hx a e, List.map_ofFn] at h
    exact (congrArg (fun q => q.left) h).symm
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext ((hu j).trans (hW' j).symm)
    rw [eu', hP] at hprod
    exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (push_ext hprod)).symm
  · intro h
    subst h
    exact ⟨W', hW', hP⟩

theorem vec_bc [IsLocalRing S] {S' : Type} [CommRing S'] [Algebra S S'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap S S') ≫ x)).obj t.G), IsUnivChart _ n xc' ∧
      ∀ cc : Fin n → S, vec t (spMap (algebraMap S S') ≫ x) xc' (algebraMap S S' ∘ cc) =
        spMap (dualMap (algebraMap S S')) ≫ vec t x xc cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := S) (R' := S') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
    (isGrpPullback_pullback t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
  refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
  have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
      (tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
    show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
  rfl

end V

theorem exists_lie_basis_stable (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X) :
    ∃ (n : ℕ) (D : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ e, IsTanAtG t x (D e)) ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (w : Sp (DualNumber S') ⟶ t.G.left),
        IsTanAtG t (spMap φ ≫ x) w →
          ∃! a : Fin n → S', IsCombAtG t (spMap φ ≫ x) (fun e => spMap (dualMap φ) ≫ D e) a w := by
  have : Smooth ((Over.pullback x).obj t.G).hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj t.G)
  refine ⟨n, fun e => vec t x xc (Pi.single e 1), fun e => vec_tan hx _, fun S' _ φ w hw => ?_⟩
  letI : Algebra S S' := φ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := S') hx
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  have hD : (fun e => spMap (dualMap φ) ≫ vec t x xc (Pi.single e 1)) =
      fun e => vec t (spMap (algebraMap S S') ≫ x) xc' (Pi.single e 1) := by
    funext e
    have h1 : (Pi.single e 1 : Fin n → S') = algebraMap S S' ∘ (Pi.single e 1 : Fin n → S) := by
      funext j
      by_cases h : j = e
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    exact (hv _).symm.trans (by rw [← h1])
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((comb_iff hx' _ _ _).1 ha).symm

end GlobalTheory.LieLocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTranslationMeasurePreserving
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump.Shear

theorem det_eq_one_of_isNilpotent_sub_one {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] V) (hf : IsNilpotent (f - 1)) : LinearMap.det f = 1 := by
  let b := Module.finBasis ℝ V
  rw [← LinearMap.det_toMatrix b]
  set B := LinearMap.toMatrix b b f with hB
  have hBB : LinearMap.toMatrixAlgEquiv b f = B := by
    ext i j; simp [hB, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have h3 : IsNilpotent (B - 1) := by
    have : B - 1 = LinearMap.toMatrixAlgEquiv b (f - 1) := by
      rw [map_sub, map_one, hBB]
    rw [this]; exact hf.map _
  have h4 : IsNilpotent (1 - B) := by rw [← neg_sub]; exact h3.neg
  have h5 := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h4).map (Polynomial.evalRingHom (1 : ℝ))
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_sub, Matrix.eval_charpoly, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, map_one, sub_sub_cancel] at h5
  exact sub_eq_zero.1 h5.eq_zero

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def above (M : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n := fun p => M p.1.1 p.1.2

def sU (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else 0

theorem nu_eq (t : Vp E n) : nu t = 1 + sU t := by
  ext i j
  simp only [nu, sU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i < j
  · simp [h, ne_of_lt h]
  · by_cases h' : i = j
    · subst h'; simp
    · simp [h, h']

theorem nu_above {M : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → M i j = 0) (hd : ∀ i, M i i = 1) :
    nu (above M) = M := by
  ext i j
  simp only [nu, above, Matrix.of_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h]
  · subst h; simp [hd]
  · simp [not_lt_of_gt h, ne_of_gt h, hl i j h]

def lin (u : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n →ₗ[ℝ] Vp E n where
  toFun t := above (sU t * u)
  map_add' a b := by
    have : sU (a + b) = sU a + sU b := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
    rw [this, Matrix.add_mul]; rfl
  map_smul' r a := by
    have : sU (r • a) = r • sU a := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp
    rw [this, Matrix.smul_mul]; rfl

theorem lin_apply (u : Matrix (Fin n) (Fin n) (Cinf E)) (t : Vp E n) : lin u t = above (sU t * u) := rfl

theorem sub_one_vanish {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0) (hd : ∀ i, u i i = 1)
    (c : ℕ) (t : Vp E n) (ht : ∀ p : Idx n, p.1.2.val < c → t p = 0) :
    ∀ p : Idx n, p.1.2.val < c + 1 → ((lin u - 1) t) p = 0 := by
  intro p hp
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only at hp hij
  rw [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, lin_apply, sub_eq_zero]
  simp only [above, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [sU, hij, hd]
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with hk | hk
    · have : sU t i k = 0 := by
        simp only [sU, Matrix.of_apply]
        split_ifs with h
        · exact ht _ (by simp only; have := Fin.lt_def.1 hk; omega)
        · rfl
      rw [this, zero_mul]
    · rw [hl k j hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem isNilpotent_lin_sub_one {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : IsNilpotent (lin u - 1) := by
  have key : ∀ m : ℕ, ∀ t : Vp E n, ∀ p : Idx n, p.1.2.val < m → (((lin u - 1) ^ m) t) p = 0 := by
    intro m
    induction m with
    | zero => intro t p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ m ih =>
      intro t p hp
      rw [pow_succ', Module.End.mul_apply]
      exact sub_one_vanish hl hd m _ (ih t) p hp
  exact ⟨n, LinearMap.ext fun t => funext fun p => key n t p p.1.2.isLt⟩

theorem det_lin {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : LinearMap.det (lin u) = 1 :=
  det_eq_one_of_isNilpotent_sub_one _ (isNilpotent_lin_sub_one hl hd)

end GlobalTheory.WhitBump.Shear


open GlobalTheory.WhitBump.Shear in
theorem GlobalTheory.WhitBump.exists_shear_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) →
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  intro E _ _ n u hu
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Vp E n)) := Measure.pi.isAddHaarMeasure _
  set L := lin (u : Matrix (Fin n) (Fin n) (Cinf E)) with hLdef
  have hdet : LinearMap.det L = 1 := det_lin hl hd
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact one_ne_zero
  let e := (LinearMap.equivOfDetNeZero L hdet0).toContinuousLinearEquiv
  let h := e.toHomeomorph.trans (Homeomorph.addLeft (above (u : Matrix (Fin n) (Fin n) (Cinf E))))
  refine ⟨h.toMeasurableEquiv, ?_, ?_⟩
  · have hL : MeasurePreserving L volume volume :=
      ⟨L.continuous_of_finiteDimensional.measurable, by
        rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, hdet]; simp⟩
    have := (measurePreserving_add_left volume (above (u : Matrix (Fin n) (Fin n) (Cinf E)))).comp hL
    exact this
  · intro t
    have hmem : nuGL t * u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) := mul_mem (nuGL_mem t) hu
    obtain ⟨hl', hd'⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hmem
    simp only [Units.val_mul, nuGL_val] at hl' hd'
    have : h.toMeasurableEquiv t = above (nu t * (u : Matrix (Fin n) (Fin n) (Cinf E))) := by
      show above _ + L t = _
      rw [hLdef, lin_apply, nu_eq, Matrix.add_mul, Matrix.one_mul]
      rfl
    rw [this, nu_above hl' hd']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDivisorDualLabel
section
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.DualDivU

section Generic

variable {L : Type} [Field L] {n : ℕ}

theorem exists_glint (O : Subring L) (A B : Matrix (Fin n) (Fin n) L) (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) :
    ∃ U ∈ GLint (Fin n) O, (U : Matrix (Fin n) (Fin n) L) = A := by
  let A0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨A i j, hA i j⟩
  let B0 : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have eA : RingHom.mapMatrix (m := Fin n) O.subtype A0 = A := by ext i j; rfl
  have eB : RingHom.mapMatrix (m := Fin n) O.subtype B0 = B := by ext i j; rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have h1 : A0 * B0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hAB])
  have h2 : B0 * A0 = 1 := inj (by rw [map_mul, map_one, eA, eB, hBA])
  exact ⟨bc (n := Fin n) O.subtype ⟨A0, B0, h1, h2⟩, ⟨_, rfl⟩, eA⟩

theorem entry_mem (O : Subring L) {U : GL (Fin n) L} (hU : U ∈ GLint (Fin n) O) (i j : Fin n) :
    (U : Matrix (Fin n) (Fin n) L) i j ∈ O := by
  obtain ⟨U0, rfl⟩ := hU
  exact ((U0 : Matrix (Fin n) (Fin n) O) i j).2

theorem antiJ_apply (i j : Fin n) : antiJ L n i j = if j = i.rev then 1 else 0 := by
  unfold antiJ
  congr 1
  have := i.2
  have := j.2
  simp only [Fin.ext_iff, Fin.val_rev, eq_iff_iff]
  omega

theorem antiJ_mul (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (antiJ L n * A) i j = A i.rev j := by
  simp [Matrix.mul_apply, antiJ_apply]

theorem mul_antiJ (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : (A * antiJ L n) i j = A i j.rev := by
  have : ∀ k : Fin n, (j = k.rev) = (k = j.rev) := fun k => by
    rw [eq_iff_iff, eq_comm, Fin.rev_eq_iff]
  simp [Matrix.mul_apply, antiJ_apply, this]

theorem antiJ_sq : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [antiJ_mul, antiJ_apply, Fin.rev_rev, Matrix.one_apply]
  simp [eq_comm]

theorem dual_mul (σ : L →+* L) (A B : Matrix (Fin n) (Fin n) L) (h : A * B = 1) :
    antiJ L n * cT σ B * antiJ L n * (antiJ L n * cT σ A * antiJ L n) = 1 := by
  calc _ = antiJ L n * cT σ B * (antiJ L n * antiJ L n) * cT σ A * antiJ L n := by simp only [Matrix.mul_assoc]
    _ = antiJ L n * cT σ (A * B) * antiJ L n := by
      rw [antiJ_sq, Matrix.mul_one, cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, cT_one, Matrix.mul_one, antiJ_sq]

theorem getD_dualLab (d : List ℤ) (hd : d.length = n) (i : Fin n) :
    (dualLab d).getD i 0 = -(d.getD i.rev 0) := by
  subst hd
  have hi := i.2
  have h1 : (i : ℕ) < (dualLab d).length := by simp [dualLab]
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ i.rev.2]
  simp only [dualLab, List.getElem_reverse, List.getElem_map, List.length_map, Fin.val_rev]
  congr 2
  omega

end Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem exists_dual (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a : GL (Fin n) L}
    (ha : a ∈ GLint (Fin n) (intL L)) :
    ∃ U ∈ GLint (Fin n) (intL L), (U : Matrix (Fin n) (Fin n) L) =
      antiJ L n * cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n := by
  have key : ∀ b ∈ GLint (Fin n) (intL L), ∀ i j,
      (antiJ L n * cT σ ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n) i j ∈ intL L := by
    intro b hb i j
    rw [mul_antiJ, antiJ_mul]
    have := entry_mem (intL L) hb j.rev i.rev
    show Valued.v (σ _) ≤ 1
    rw [hσ]
    exact this
  exact exists_glint (intL L) _ (antiJ L n * cT σ (a : Matrix (Fin n) (Fin n) L) * antiJ L n)
    (dual_mul σ _ _ (Units.mul_inv a)) (dual_mul σ _ _ (Units.inv_mul a)) (key _ (inv_mem ha)) (key _ ha)

theorem hasDiv_dualLab : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (d : List ℤ) (g : GL (Fin n) L), (∀ x, Valued.v (σ x) = Valued.v x) → d.length = n → g ∈ GU σ n → HasDiv (intL L) d g → HasDiv (intL L) (dualLab d) g := by
  intro L _ _ σ n d g hσ hd hg ⟨ϖ, hϖ, a, ha, b, hb, hab⟩
  obtain ⟨a', ha', ea⟩ := exists_dual σ hσ ha
  obtain ⟨b', hb', eb⟩ := exists_dual σ hσ hb
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  refine ⟨σ ϖ, by rw [hσ, hϖ], a', ha', b', hb', ?_⟩
  have hg' : cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = antiJ L n := hg
  have eD : Matrix.diagonal (fun i : Fin n => σ ϖ ^ (dualLab d).getD i 0) =
      antiJ L n * cT σ (Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) * antiJ L n := by
    ext i j
    rw [mul_antiJ, antiJ_mul]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply, Fin.rev_inj]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [getD_dualLab d hd, map_zpow₀]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hDD : Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero]
  have hinv : (g : Matrix (Fin n) (Fin n) L) * (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) = 1 := by
    rw [hab]
    calc _ = (a : Matrix (Fin n) (Fin n) L) * (Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) *
        ((b : Matrix (Fin n) (Fin n) L) * ((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
        Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0))) *
        ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hDD, Matrix.mul_one, Units.mul_inv]
  have h1 := dual_mul σ _ _ hinv
  have h2 : antiJ L n * cT σ (g : Matrix (Fin n) (Fin n) L) * antiJ L n * (g : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _), hg', antiJ_sq]
  have h3 : (g : Matrix (Fin n) (Fin n) L) = antiJ L n * cT σ (((b⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Matrix.diagonal (fun i : Fin n => ϖ ^ (-d.getD i 0)) * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
      antiJ L n := by
    conv_rhs => rw [← Matrix.mul_one (_ * antiJ L n), ← h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h3, ea, eb, eD, cT_mul, cT_mul]
  have hJ : ∀ X : Matrix (Fin n) (Fin n) L, antiJ L n * (antiJ L n * X) = X := fun X => by
    rw [← Matrix.mul_assoc, antiJ_sq, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hJ]

end GlobalTheory.DualDivU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelf
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem frobR_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  intro p _ K hK r hr x
  have hit : ∀ (i : ℕ) (y : Kn p K r),
      (((⇑(frobR p K r))^[i] y : Kn p K r) : PadicAlgCl p) = (frobK p K ^ i) (y : PadicAlgCl p) := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
      rfl
  apply Subtype.ext
  rw [hit]
  exact (IsFrobOn.pow_fixes_iff p K hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ x.2

end GlobalTheory.LKLoc
end

