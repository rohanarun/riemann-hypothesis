module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoBaseChangesOfCongruentMapsPureHodge
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.PureTower

open ReciprocityTheory.ChartRestriction.G.Out (thick thickTrans thickObj thickMap thickTrans_comp)

theorem exists_end {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : G' ⟶ G', IsMonHom U ∧ U.left ≫ φ = φ ≫ W.left := by
  let U : G' ⟶ G' := Over.homMk (h.1.lift (φ ≫ W.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w]))
    (h.1.lift_snd _ _ _)
  have e : U.left ≫ φ = φ ≫ W.left := h.1.lift_fst _ _ _
  exact ⟨U, Out.PullGtPf.isMonHom_of_grpPullback h h W U e, e⟩

variable {T : Type} [CommRing T] (I : Ideal T)

theorem thickMap_fst (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ pullback.fst A.hom (thick T I (e + 1)) = pullback.fst A.hom (thick T I e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem thickMap_hom (e : ℕ) (A : Over (Sp T)) :
    thickMap T I e A ≫ (thickObj T I (e + 1) A).hom = (thickObj T I e A).hom ≫ thickTrans T I e :=
  pullback.lift_snd _ _ _

theorem isGrpPullback_thickMap (e : ℕ) (A : Over (Sp T)) [GrpObj A] :
    IsGrpPullback (thickObj T I e A) (thickObj T I (e + 1) A) (thickTrans T I e) (thickMap T I e A) :=
  (isGrpPullback_pullback A _).cancel
    ((isGrpPullback_pullback A _).congr (thickTrans_comp T I e).symm (thickMap_fst I e A).symm) (thickMap_hom I e A)

theorem ker_factor_sq (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2
      = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ]
  exact Ideal.mul_mem_mul hx (Ideal.pow_le_self (Nat.succ_ne_zero e) hy)

variable {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G]

theorem isGrpPullback_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (e : ℕ) :
    IsGrpPullback (thickObj T I e A) G (spMap ((Ideal.Quotient.mk (I ^ (e + 1))).comp a))
      (pullback.fst A.hom (thick T I e) ≫ φ) :=
  ((isGrpPullback_pullback A _).comp h).congr (by rw [← Spec.map_comp]; rfl) rfl

theorem exists_end_red {a : S →+* T} {A : Over (Sp T)} [GrpObj A] {φ : A.left ⟶ G.left}
    (h : IsGrpPullback A G (spMap a) φ) (W : G ⟶ G) [IsMonHom W] :
    ∃ U : ∀ e, thickObj T I e A ⟶ thickObj T I e A, (∀ e, IsMonHom (U e)) ∧
      (∀ e, (U e).left ≫ pullback.fst A.hom (thick T I e) ≫ φ = (pullback.fst A.hom (thick T I e) ≫ φ) ≫ W.left) ∧
      ∀ e, thickMap T I e A ≫ (U (e + 1)).left = (U e).left ≫ thickMap T I e A := by
  choose U hU eU using fun e => exists_end (isGrpPullback_red I h e) W
  refine ⟨U, hU, eU, fun e => (isGrpPullback_red I h (e + 1)).1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, eU, Category.assoc (U e).left, ← Category.assoc (thickMap T I e A),
      ← Category.assoc (thickMap T I e A), thickMap_fst, eU]
  · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, ← Category.assoc, Over.w]

theorem existsUnique_hom (hF : GlobalTheory.Published.FormalAlgebraisation) (hM : GlobalTheory.Published.GrothendieckMessing) {g : ℕ}
    (hG : IsAbelianScheme G) (hg : SmoothOfRelativeDimension g G.hom) (W : G ⟶ G) [IsMonHom W] {r s : S}
    (hW : IsPureBC G W r s) [IsNoetherianRing T] (hI : IsAdicComplete I T) {p : ℕ} (hp : p.Prime) (hpI : (p : T) ∈ I)
    {a b : S →+* T} (hab : ∀ x, a x - b x ∈ I) (hu : IsUnit (a r - b s)) {A B : Over (Sp T)} [GrpObj A] [GrpObj B]
    {φ : A.left ⟶ G.left} {ψ : B.left ⟶ G.left} (hA : IsGrpPullback A G (spMap a) φ)
    (hB : IsGrpPullback B G (spMap b) ψ) :
    ∃! F : A ⟶ B, IsMonHom F ∧ ∀ (X : Scheme.{0}) (x : X ⟶ A.left) (t : X ⟶ Sp (T ⧸ I ^ (0 + 1))),
      x ≫ A.hom = t ≫ thick T I 0 → x ≫ F.left ≫ ψ = x ≫ φ := by
  obtain ⟨U, hU, eU, cU⟩ := exists_end_red I hA W
  obtain ⟨V, hV, eV, cV⟩ := exists_end_red I hB W
  have rA := isGrpPullback_red I hA
  have rB := isGrpPullback_red I hB
  have e0 : (Ideal.Quotient.mk (I ^ (0 + 1))).comp a = (Ideal.Quotient.mk (I ^ (0 + 1))).comp b :=
    RingHom.ext fun x => Ideal.Quotient.eq.2 (by simpa using hab x)
  obtain ⟨f₀, hf₀, ef₀⟩ := grpPullback_iso (rA 0) ((rB 0).congr (by rw [e0]) rfl)
  let P : ℕ → Type := fun e => {f : thickObj T I e A ⟶ thickObj T I e B // IsMonHom f ∧ U e ≫ f = f ≫ V e}
  have step : ∀ (e : ℕ) (f : P e), ∃ f' : P (e + 1), thickMap T I e A ≫ f'.1.left = f.1.left ≫ thickMap T I e B ∧
      ∀ k : thickObj T I (e + 1) A ⟶ thickObj T I (e + 1) B, IsMonHom k →
        thickMap T I e A ≫ k.left = f.1.left ≫ thickMap T I e B → k = f'.1 := by
    intro e f
    have := f.2.1
    obtain ⟨k, h₁, h₂, h₃, h₄⟩ := _root_.GlobalTheory.pureLift_step hM p hp _ _
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))
      ⟨e + 1 + 1, by
        rw [← map_natCast (Ideal.Quotient.mk (I ^ (e + 1 + 1))), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hpI _⟩
      (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) g g _ _ _ _ _ _
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rA (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rA (e + 1)).1 hg)
      (PolPull.isAbelianScheme_of_isGrpPullback hG (rB (e + 1)))
      ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (rB (e + 1)).1 hg)
      (isGrpPullback_thickMap I e A) (isGrpPullback_thickMap I e B) (U (e + 1)) (V (e + 1)) (U e) (V e) (cU e) (cV e)
      _ _ _ _ (hW _ _ _ _ (rA (e + 1)) _ (eU _)) (hW _ _ _ _ (rB (e + 1)) _ (eV _))
      (by simpa using hu.map (Ideal.Quotient.mk (I ^ (e + 1 + 1)))) f.1 f.2.2
    exact ⟨⟨k, h₁, h₃⟩, h₂, h₄⟩
  choose nx h₁ h₂ using step
  have c₀ : U 0 ≫ f₀.hom = f₀.hom ≫ V 0 := Over.OverMorphism.ext ((rB 0).1.hom_ext
    (by rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, ef₀, eU, eV, ← Category.assoc f₀.hom.left,
      ef₀]) (by rw [Over.w, Over.w]))
  let f : ∀ e, P e := fun e => Nat.rec ⟨f₀.hom, hf₀, c₀⟩ nx e
  obtain ⟨F, hF₁, hF₂, hF₃⟩ := GlobalTheory.grpHom_algebraise hF.1 T I hI A B
    (PolPull.isAbelianScheme_of_isGrpPullback hG hA).proper (PolPull.isAbelianScheme_of_isGrpPullback hG hB).proper
    (fun e => thickObj T I e A) (fun e => thickObj T I e B) (fun e => thickMap T I e A) (fun e => thickMap T I e B)
    _ _ (fun e => isGrpPullback_pullback A _) (fun e => thickMap_fst I e A) (fun e => isGrpPullback_pullback B _)
    (fun e => thickMap_fst I e B) (fun e => (f e).1) (fun e => (f e).2.1) (fun e => h₁ e (f e))
  refine ⟨F, ⟨hF₁, fun X x t ht => ?_⟩, fun K ⟨hK, eK⟩ => hF₃ K fun e => ?_⟩
  · have h0 : pullback.fst A.hom (thick T I 0) ≫ F.left = f₀.hom.left ≫ pullback.fst B.hom (thick T I 0) := hF₂ 0
    rw [← pullback.lift_fst x t ht, Category.assoc, Category.assoc, ← Category.assoc _ F.left, h0, Category.assoc, ef₀]
  · have n : ∀ e, ((Over.pullback (thick T I e)).map K).left ≫ pullback.fst B.hom (thick T I e) =
        pullback.fst A.hom (thick T I e) ≫ K.left := fun e => pullback.lift_fst _ _ _
    have key : ∀ e, (Over.pullback (thick T I e)).map K = (f e).1 := by
      intro e
      induction e with
      | zero =>
        refine Over.OverMorphism.ext ((rB 0).1.hom_ext ?_ (by rw [Over.w, Over.w]))
        rw [← Category.assoc, n, Category.assoc, eK _ _ _ pullback.condition]
        exact ef₀.symm
      | succ e ih =>
        refine h₂ e (f e) _ inferInstance ?_
        rw [← ih]
        refine (isGrpPullback_pullback B (thick T I (e + 1))).1.hom_ext ?_ ?_
        · rw [Category.assoc, n, ← Category.assoc, thickMap_fst, Category.assoc, thickMap_fst, n]
        · rw [Category.assoc, Over.w, Category.assoc, thickMap_hom, thickMap_hom, ← Category.assoc, Over.w]
    rw [← key, n]

theorem exists_isGrpPullback_of_congr : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (S : Type) [CommRing S] (G : Over (Sp S)) [GrpObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (W : G ⟶ G) [IsMonHom W] (r s : S), IsPureBC G W r s → ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T], IsAdicComplete (IsLocalRing.maximalIdeal T) T → ∀ p : ℕ, p.Prime → (p : T) ∈ IsLocalRing.maximalIdeal T → ∀ a b : S →+* T, (∀ x, a x - b x ∈ IsLocalRing.maximalIdeal T) → IsUnit (a (r - s)) → ∀ (A : Over (Sp T)) [GrpObj A] (φ : A.left ⟶ G.left), IsGrpPullback A G (spMap a) φ → ∃ φ' : A.left ⟶ G.left, IsGrpPullback A G (spMap b) φ' ∧ ∀ x : Sp (IsLocalRing.ResidueField T) ⟶ A.left, x ≫ A.hom = spMap (IsLocalRing.residue T) → x ≫ φ = x ≫ φ' := by
  intro hF hM S _ G _ g hG hg W _ r s hW T _ _ _ hI p hp hpI a b hab hu A _ φ hA
  have hB := isGrpPullback_pullback G (spMap b)
  have hba : ∀ x, b x - a x ∈ IsLocalRing.maximalIdeal T := fun x => by
    simpa using neg_mem (hab x)
  have un : ∀ y z : T, IsUnit y → z ∈ IsLocalRing.maximalIdeal T → IsUnit (y + z) := fun y z hy hz => by
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal y).1
      (by simpa using sub_mem ((IsLocalRing.mem_maximalIdeal _).2 h) hz) hy
  rw [map_sub] at hu
  have u₁ : IsUnit (a r - b s) := by simpa using un _ _ hu (hab s)
  have u₂ : IsUnit (b r - a s) := by
    have := un _ _ hu (hba r)
    rwa [add_comm, sub_add_sub_cancel] at this
  have u₃ : IsUnit (b r - b s) := by simpa using un _ _ u₂ (hab s)
  obtain ⟨F, ⟨hF₁, hF₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hab u₁ hA hB
  obtain ⟨K, ⟨hK₁, hK₂⟩, -⟩ := existsUnique_hom _ hF hM hG hg W hW hI hp hpI hba u₂ hB hA
  have FK : F ≫ K = 𝟙 A := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) hu hA hA).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hK₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hF₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  have KF : K ≫ F = 𝟙 _ := (existsUnique_hom _ hF hM hG hg W hW hI hp hpI (fun x => by simp) u₃ hB hB).unique
    ⟨inferInstance, fun X x t ht => by
      rw [Over.comp_left, Category.assoc, ← Category.assoc x, hF₂ _ _ t (by rw [Category.assoc, Over.w, ht]),
        Category.assoc, hK₂ _ _ t ht]⟩ ⟨inferInstance, fun X x t ht => by simp⟩
  refine ⟨F.left ≫ _, ((isGrpPullback_of_iso ⟨F, K, FK, KF⟩).comp hB).congr (Category.id_comp _) rfl,
    fun x hx => (hF₂ _ x (spMap (Ideal.Quotient.lift _ (IsLocalRing.residue T) fun y hy =>
      (IsLocalRing.residue_eq_zero_iff y).2 (by simpa using hy))) ?_).symm⟩
  rw [hx, ← Spec.map_comp]
  rfl

end GlobalTheory.PureTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpecFiniteFreeOfFiniteFlat
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

namespace GlobalTheory.FiniteFlatLocal

theorem exists_finFree_local : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ s : S, ∃ (W : S.Opens) (A B : Type) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Free A B) (_ : Module.Finite A B) (eW : W.toScheme ≅ Spec (CommRingCat.of A)) (eZ : (z ⁻¹ᵁ W).toScheme ≅ Spec (CommRingCat.of B)), s ∈ W ∧ eZ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = (z ∣_ W) ≫ eW.hom := by
  intro S Z z h1 h2 h3 s
  obtain ⟨V, hV, hsV, -, hF⟩ := GlobalTheory.FiniteAmpleFP.exists_finFree_app_fp z (x := s) (U := ⊤) trivial
  have hZ : IsAffineOpen (z ⁻¹ᵁ V) := hV.preimage z
  letI : Algebra Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := (z.app V).hom.toAlgebra
  have hfin : Module.Finite Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.1
  have hfree : Module.Free Γ(S, V) Γ(Z, z ⁻¹ᵁ V) := hF.2
  refine ⟨V, Γ(S, V), Γ(Z, z ⁻¹ᵁ V), inferInstance, inferInstance, inferInstance, hfree, hfin,
    hV.isoSpec, hZ.isoSpec, hsV, ?_⟩
  have e := IsAffineOpen.SpecMap_appLE_fromSpec z hV hZ le_rfl
  rw [← Scheme.Hom.app_eq_appLE] at e
  rw [← cancel_mono (hV.isoSpec.inv ≫ V.ι)]
  rw [IsAffineOpen.isoSpec_inv_ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    morphismRestrict_ι, ← IsAffineOpen.isoSpec_hom_fromSpec hZ, Category.assoc, ← e]
  rfl

end GlobalTheory.FiniteFlatLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace SplitOffPlaces
open _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory

noncomputable def conjSpec {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 E) where
  asIdeal := P.asIdeal.comap (cO E)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : cO E x ∈ P.asIdeal.comap (cO E) := by
      rw [Ideal.mem_comap, cO_cO]; exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← cO_cO x, h1, map_zero]

theorem exists_mem_not_mem {A : Type} [CommRing A] [IsDedekindDomain A] {Q P P' : HeightOneSpectrum A}
    (h : Q ≠ P) (h' : Q ≠ P') : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal ∧ x ∉ P'.asIdeal := by
  by_contra hc
  have hs : (Q.asIdeal : Set A) ⊆ (P.asIdeal : Set A) ∪ (P'.asIdeal : Set A) := by
    intro x hx
    by_contra hx'
    exact hc ⟨x, hx, fun h1 => hx' (Or.inl h1), fun h1 => hx' (Or.inr h1)⟩
  rcases Ideal.subset_union.1 hs with h1 | h1
  · exact h (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1))
  · exact h' (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P'.isPrime.ne_top h1))

theorem star_sqrt (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  haveI := D.host.isCMField_hostE
  have h2 : D.host.φ₀ (star D.host.sqrtMinusD) = starRingEnd ℂ (D.host.φ₀ D.host.sqrtMinusD) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ D.host.sqrtMinusD
  rw [h2, map_neg, h1]
  simp

theorem sqrt_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem exists_coord (D : D7) (x : D.host.E) (hx : x ∈ D.host.K) :
    ∃ u v : ℚ, x = (u : D.host.E) + (v : D.host.E) * D.host.sqrtMinusD := by
  have halg : IsAlgebraic ℚ D.host.sqrtMinusD := Algebra.IsAlgebraic.isAlgebraic _
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqrtMinusD} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, 1, by rw [Set.mem_singleton_iff.1 hy]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - D.host.d * v * v', u * v' + v * u', ?_⟩
    push_cast
    linear_combination (v * v' : D.host.E) * sqrt_sq D

theorem exists_norm (D : D7) (x : 𝓞 D.host.K) :
    ∃ (x' : 𝓞 D.host.K) (n : ℤ), algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x' = cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) ∧
      x * x' = (n : 𝓞 D.host.K) := by
  obtain ⟨u, v, huv⟩ := exists_coord D ((x : D.host.K) : D.host.E) (x : D.host.K).2
  have hb : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hst : star ((x : D.host.K) : D.host.E) = (u : D.host.E) - (v : D.host.E) * D.host.sqrtMinusD := by
    rw [huv, star_add, star_mul, star_sqrt, star_ratCast, star_ratCast]; ring
  have hmem : star ((x : D.host.K) : D.host.E) ∈ D.host.K := by
    rw [hst]
    exact sub_mem (SubfieldClass.ratCast_mem _ u) (mul_mem (SubfieldClass.ratCast_mem _ v) hb)
  have hinj : Function.Injective (algebraMap D.host.K D.host.E) := (algebraMap D.host.K D.host.E).injective
  have hint : IsIntegral ℤ (⟨_, hmem⟩ : D.host.K) := by
    rw [← isIntegral_algebraMap_iff (B := D.host.E)]
    exact (cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x)).isIntegral_coe
  let x' : 𝓞 D.host.K := ⟨⟨_, hmem⟩, hint⟩
  have hq : ((x * x' : 𝓞 D.host.K) : D.host.K) = algebraMap ℚ D.host.K (u ^ 2 + D.host.d * v ^ 2) := by
    apply hinj
    have e1 : algebraMap D.host.K D.host.E ((x * x' : 𝓞 D.host.K) : D.host.K) =
      ((x : D.host.K) : D.host.E) * star ((x : D.host.K) : D.host.E) := rfl
    rw [e1, hst, ← IsScalarTower.algebraMap_apply, huv, eq_ratCast]
    push_cast
    linear_combination (-(v : D.host.E) ^ 2) * sqrt_sq D
  have hi : IsIntegral ℤ (u ^ 2 + D.host.d * v ^ 2 : ℚ) := by
    rw [← isIntegral_algebraMap_iff (B := D.host.K), ← hq]
    exact (x * x').isIntegral_coe
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨x', n, RingOfIntegers.ext rfl, RingOfIntegers.ext ?_⟩
  rw [hq, ← hn]
  simp

end SplitOffPlaces


open SplitOffPlaces _root_.Formalism.L2.Col Formalism.HermitianLatticesTheory in
theorem splitOff_places : ∀ {D : D7} (Pb : Formalism.L2.Host.PiBar D.host) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (P : HeightOneSpectrum (𝓞 D.host.E)), (∀ PP, PP ∈ Pg ↔ ∃ k, Pb.Div k PP) → (∀ v ∈ S, ∃ PP ∈ Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) → Formalism.IndefR.Bridge.SplitOff P (Pg : Set (HeightOneSpectrum (𝓞 D.host.E))) → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ (∀ PP ∈ Pg, PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) ∧ OffS D S P := by
  intro D Pb Pg S P hPg hS hP
  obtain ⟨-, hP1, hP2⟩ := hP
  have hne : ∀ PP ∈ Pg, PP ≠ P := fun PP h e => hP1 (e ▸ h)
  have hne' : ∀ PP ∈ Pg, PP ≠ conjSpec P := fun PP h e => hP2 PP h (by rw [e, conjIdeal_eq]; rfl)
  have hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro k hk
    have h1 : Pb.pb k ≠ P.under (𝓞 D.host.K) := fun e => hne P ((hPg P).2 ⟨k, e.symm⟩) rfl
    have h2 : Pb.pb k ≠ (conjSpec P).under (𝓞 D.host.K) := fun e =>
      hne' (conjSpec P) ((hPg _).2 ⟨k, e.symm⟩) rfl
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem h1 h2
    obtain ⟨x', n, hx', hn⟩ := exists_norm D x
    have hnP : (n : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      have e : (n : 𝓞 D.host.E) = algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x * cO D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) x) := by
        rw [← hx', ← map_mul, hn, map_intCast]
      rw [e] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    have hnb : (n : 𝓞 D.host.K) ∈ (Pb.pb k).asIdeal := hn ▸ Ideal.mul_mem_right _ _ hx
    have hp : Prime (D.host.g k : ℤ) := Nat.prime_iff_prime_int.1 (D.host.g_prime k)
    by_cases hd : (D.host.g k : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hd
      apply hnP
      push_cast
      exact Ideal.mul_mem_right _ _ hk
    · obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).2 hd
      apply (Pb.pb k).isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 D.host.K) = a * ((D.host.g k : ℕ) : 𝓞 D.host.K) + b * n := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hab.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Pb.pb_over k)) (Ideal.mul_mem_left _ _ hnb)
  refine ⟨?_, fun PP h => ⟨hne PP h, fun hc => hne' PP h ?_⟩, ?_⟩
  · intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hg 0 h
    · exact hg 1 h
  · refine HeightOneSpectrum.ext (PP.isMaximal.eq_of_le (conjSpec P).isPrime.ne_top fun c hc' => ?_)
    obtain ⟨c', h1, h2⟩ := hc c hc'
    have e : cO D.host.E c = c' := RingOfIntegers.ext h2.symm
    change cO D.host.E c ∈ P.asIdeal
    rwa [e]
  · intro v hv
    obtain ⟨PP, hPP, rfl⟩ := hS v hv
    obtain ⟨x, hx, hx1, hx2⟩ := exists_mem_not_mem (hne PP hPP) (hne' PP hPP)
    have hfix : star ((x * cO D.host.E x : 𝓞 D.host.E) : D.host.E) = ((x * cO D.host.E x : 𝓞 D.host.E) : D.host.E) := by
      change star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul, star_star]
    obtain ⟨a, ha⟩ := (D.sp.cm.fixed _).1 hfix
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (B := D.host.E), ha]
      exact (x * cO D.host.E x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ = x * cO D.host.E x := RingOfIntegers.ext ha
    refine ⟨⟨a, hint⟩, ?_, fun y hy hyP => ?_⟩
    · change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨a, hint⟩ ∈ PP.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    · have e' : y = x * cO D.host.E x := RingOfIntegers.ext (hy.trans ha)
      rw [e'] at hyP
      rcases P.isPrime.mem_or_mem hyP with h | h
      · exact hx1 h
      · exact hx2 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMirabolicScalarUnitaryDecompositionArchime
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix

namespace GlobalTheory.IwasawaLast

theorem exists_unitary_lastRow {n : ℕ} (ℓ : Fin (n + 1) → ℂ) (hℓ : ℓ ≠ 0) :
    ∃ r : ℂ, r ≠ 0 ∧ ∃ k ∈ unitaryGroup (Fin (n + 1)) ℂ, ∀ l, ℓ l = r * k (Fin.last n) l := by
  set x : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (star ℓ) with hx
  have hx0 : x ≠ 0 := by
    intro h
    apply hℓ
    have : star ℓ = 0 := by
      have := congrArg WithLp.ofLp h
      simpa [hx] using this
    simpa using congrArg star this
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  set w : EuclideanSpace ℂ (Fin (n + 1)) := ((‖x‖ : ℂ)⁻¹) • x with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul]
    simp [hn]
  have hon : Orthonormal ℂ (({Fin.last n} : Set (Fin (n + 1))).domRestrict (fun _ => w)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_singleton_iff] at hi hj
    subst hi; subst hj
    simp [Set.domRestrict, inner_self_eq_norm_sq_to_K, hw1]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hbl : b (Fin.last n) = w := hb _ (Set.mem_singleton _)
  set M := (EuclideanSpace.basisFun (Fin (n + 1)) ℂ).toBasis.toMatrix b with hM
  have hMu : M ∈ unitaryGroup (Fin (n + 1)) ℂ :=
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _
  refine ⟨(‖x‖ : ℂ), by exact_mod_cast hn, star M, ?_, ?_⟩
  · exact Unitary.star_mem hMu
  · intro l
    simp [hM, Matrix.star_apply, Module.Basis.toMatrix_apply, hbl, hw, hx]
    have hn' : ((‖WithLp.toLp 2 (star ℓ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul]

end GlobalTheory.IwasawaLast

namespace GlobalTheory.IwasawaLast

theorem iwasawa_lastRow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (y : GL (Fin (m + 1)) (Cinf E)), ∃ (p : GL (Fin (m + 1)) (Cinf E)) (ρ : (Cinf E)ˣ) (k : Kinf E (m + 1)), (∀ j, (p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧ y = p * Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom ρ * Unitary.toUnits k := by
  intro E _ _ _ m y
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) with hY
  set ℓ : InfinitePlace E → Fin (m + 1) → ℂ := fun v j => Y (Fin.last m) j v with hℓdef
  have hne : ∀ v, ℓ v ≠ 0 := by
    intro v h
    have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp (Units.isUnit y)
    have hv : IsUnit (Y.det v) := (Pi.isUnit_iff.mp hdet) v
    have hmap : Y.det v = ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det :=
      RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v) Y
    have h0 : ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v).mapMatrix Y).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero (Fin.last m) (fun j => by
        simpa [hℓdef] using congrFun h j)
    rw [hmap, h0] at hv
    exact not_isUnit_zero hv
  choose r hr kv hkv hℓ using fun v => exists_unitary_lastRow (ℓ v) (hne v)
  set K : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E) := Matrix.of fun i j v => kv v i j with hKdef
  have hK : K ∈ unitaryGroup (Fin (m + 1)) (Cinf E) := by
    rw [mem_unitaryGroup_iff]
    ext i j v
    have := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) i) j
    by_cases hij : i = j <;> simp [hKdef, Matrix.mul_apply, Finset.sum_apply, Matrix.star_apply, Matrix.one_apply, hij] at this ⊢ <;> exact this
  have hρ : IsUnit (fun v => r v : Cinf E) := Pi.isUnit_iff.mpr fun v => (hr v).isUnit
  refine ⟨y * (Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ *
      (Units.map (Matrix.scalar (Fin (m + 1)) : Cinf E →+* Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)).toMonoidHom hρ.unit)⁻¹,
    hρ.unit, ⟨K, hK⟩, ?_, by group⟩
  intro j
  ext v
  have hinv : (((Unitary.toUnits (⟨K, hK⟩ : Kinf E (m + 1)))⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) = star K := rfl
  have hρv : ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E) v = (r v)⁻¹ := by
    have h1 := congrFun hρ.unit.inv_mul v
    simp only [Units.val_mul, Pi.mul_apply, IsUnit.unit_spec, Units.val_one, Pi.one_apply] at h1
    exact eq_inv_of_mul_eq_one_left h1
  have hrow : ∀ l, Y (Fin.last m) l v = r v * kv v (Fin.last m) l := fun l => hℓ v l
  have hu := congrFun (congrFun (mem_unitaryGroup_iff.mp (hkv v)) (Fin.last m)) j
  simp only [Units.val_mul, Units.coe_map_inv, MonoidHom.coe_coe, hinv]
  rw [← hY]
  show (Y * star K * Matrix.scalar (Fin (m + 1)) ((hρ.unit⁻¹ : (Cinf E)ˣ) : Cinf E)) (Fin.last m) j v = _
  rw [Matrix.scalar_apply, Matrix.mul_diagonal]
  simp only [Matrix.scalar_apply, Matrix.mul_diagonal, Pi.mul_apply, hρv, Matrix.mul_apply, Finset.sum_apply, hrow, Matrix.star_apply, Pi.star_apply, hKdef, Matrix.of_apply] at hu ⊢
  have hs : ∑ x, r v * kv v (Fin.last m) x * star (kv v j x) = r v * ∑ x, kv v (Fin.last m) x * star (kv v j x) := by
    rw [Finset.mul_sum]; simp [mul_assoc]
  rw [hs, hu, Matrix.one_apply]
  by_cases hj : j = Fin.last m
  · subst hj; simp [hr v]
  · simp [hj, Ne.symm hj]

end GlobalTheory.IwasawaLast
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionAtIffKottwitzModuleCondiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorLieConditionAt_iff_kottwitzModuleCondition : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S),
    LieAt b act β x ↔
      LieMod (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D)) D.ω (β b.ρ) (fun i => β.comp (b.t i)) := by
  first | exact @GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod | exact GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod | (intros; apply GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod <;> assumption)
end

