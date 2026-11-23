module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1933
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pmap2 {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ (A ⊗ T) ⟶ A' ⊗ (A' ⊗ T) :=
  lift (fst A (A ⊗ T) ≫ q) (snd A (A ⊗ T) ≫ pmap q T)

def ptFst (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)

def ptSnd (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

def ptMul (A T : Over S) [MonObj A] : A ⊗ (A ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)

def addBundle {A T : Over S} [MonObj A] (M : LB (A ⊗ T).left) : LB (A ⊗ (A ⊗ T)).left :=
  LB.div (tens (ev M (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
      (ev M (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)))
    (ev M (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T))

theorem preimage_le_of_comp {X Y Z W : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (h : f ≫ g = f' ≫ g') (U : W.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f' ⁻¹ᵁ (g' ⁻¹ᵁ U) := by
  intro x hx
  have e : g.base (f.base x) = g'.base (f'.base x) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  show g'.base (f'.base x) ∈ U
  rw [← e]
  exact hx

theorem prodMapPairTimesIdentity_fst {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptFst A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptFst, pmap]

theorem prodMapPairTimesIdentity_snd {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (snd A' (A' ⊗ T) ≫ fst A' T) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptSnd A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptSnd, pmap]

theorem prodMapPairTimesIdentity_mul {A A' : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T) * (snd A' (A' ⊗ T) ≫ fst A' T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptMul A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptMul, pmap, MonObj.comp_mul, MonObj.mul_comp]

theorem addGen_le₁ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptFst A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_fst q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.1 PUnit.unit hx.1.1

theorem addGen_le₂ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptSnd A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_snd q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.2 PUnit.unit hx.1.2

theorem addGen_le₃ {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptMul A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_mul q T) _)
  intro x hx
  exact LB.wchart_le M _ k.2 PUnit.unit hx.2

def addGen {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι) :
    Γ((A ⊗ (A ⊗ T)).left, (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)ˣ :=
  res (addGen_le₁ q M k) (pullU (ptFst A T).left _ (e (k.1.1 PUnit.unit))) *
    res (addGen_le₂ q M k) (pullU (ptSnd A T).left _ (e (k.1.2 PUnit.unit))) *
    (res (addGen_le₃ q M k) (pullU (ptMul A T).left _ (e (k.2 PUnit.unit))))⁻¹

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelPull

theorem push_sec_of_left {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hpb : IsGrpPullback A' A f φ) {x : 𝟙_ (Over S) ⟶ A} {x' : 𝟙_ (Over S') ⟶ A'}
    (hx : x'.left ≫ φ = f ≫ x.left) (T : Over S') :
    pushHom hpb T (toUnit T ≫ x') = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ x'.left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, hx, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem isSympLev_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left} {φ₂ : (G2 A').left ⟶ (G2 A).left}
    (hpb : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (G2 A).left} {P' : LB (G2 A').left}
    (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) {h M : ℕ} {B : Type} [CommRing B] {ζ : B}
    {s : S ⟶ Sp B} {lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)}
    {lev' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ A')} (hl : ∀ a, (lev' a).left ≫ φ = f ≫ (lev a).left)
    (hS : IsSympLev P h M ζ s lev) : IsSympLev P' h M ζ (f ≫ s) lev' := by
  have hp' : ∀ a, pushHom hpb _ (lev' a) = toUnit _ ≫ lev a := fun a => by
    have e := push_sec_of_left hpb (hl a) (𝟙_ (Over S'))
    rwa [toUnit_unit, Category.id_comp] at e
  refine ⟨fun a b => push_injective hpb _ ?_, fun a => push_injective hpb _ ?_, ?_⟩
  · rw [map_mul, hp', hp', hp', hS.1, MonObj.comp_mul]
  · rw [map_pow, map_one, hp', ← MonObj.comp_pow, hS.2.1, MonObj.comp_one]
  intro k _ _ x β z hx hz
  obtain ⟨g₁, g₂, g₃⟩ := hS.2.2 k (x ≫ f) β z (by rw [Category.assoc, hx]) hz
  refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
  · rw [← (push_injective hpb (Over.mk x)).eq_iff, push_sec_of_left hpb (hl a), map_one]
    rfl
  · obtain ⟨a, ha⟩ := g₂ (pushHom hpb (Over.mk x) g) (by
      have := congrArg (pushHom hpb (Over.mk x)) hg
      rw [map_pow, map_one] at this
      exact this)
    exact ⟨a, push_injective hpb _ ((push_sec_of_left hpb (hl a) _).trans ha)⟩
  · exact (weilIs_grpPullback_of_comm S S' A A' f φ _ _ (pull_isLB hP _) (pull_isLB hP' _) hpb
      (diag_iso sq H) (Over.mk x) M _ _ _ _ _
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl a) (Over.mk x)).symm)
      (congrArg (fun q => q.left) (push_sec_of_left hpb (hl b) (Over.mk x)).symm)).2 (g₃ a b)

theorem kerBy_pull {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂)
    {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (d : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ d = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ d = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ?_
  rw [map_pow, map_one]
  refine hn _ (pushHom h T x) ?_
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

theorem siegKerBy_pull {S S' : Scheme.{0}} {h M : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c : SiegPre h M ζ s} {c' : SiegPre h M ζ' s'} {f : S' ⟶ S}
    (m : SiegPB c' c f) {d : ℕ} (hc : SiegKerBy c d) : SiegKerBy c' d := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := m
  exact ⟨(GlobalTheory.pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 hc.1, kerBy_pull pb sq c.isLB c'.isLB iso d hc.2⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutQuotientSurjectiveKerEqMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pushout_quotient_map_eq_quotient_map_ideal : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  intro R C E _ _ _ c f π χ h
  have hw' : ∀ r, π (f r) = χ (Ideal.Quotient.mk c r) := fun r => by
    have := congrArg (fun g => g.hom r) h.w
    simpa using this
  have hle : c.map f ≤ RingHom.ker π := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp [RingHom.mem_ker, hw', Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  let q : C →+* C ⧸ c.map f := Ideal.Quotient.mk _
  let qm : R ⧸ c →+* C ⧸ c.map f := Ideal.quotientMap (c.map f) f Ideal.le_comap_map
  let φ : C ⧸ c.map f →+* E := Ideal.Quotient.lift _ π (fun x hx => hle hx)
  have hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Ideal.Quotient.mk c) ≫ CommRingCat.ofHom qm := by
    ext r; rfl
  let ψ := h.desc (CommRingCat.ofHom q) (CommRingCat.ofHom qm) hcomm
  have h1 : CommRingCat.ofHom π ≫ ψ = CommRingCat.ofHom q := h.inl_desc _ _ _
  have h2 : CommRingCat.ofHom χ ≫ ψ = CommRingCat.ofHom qm := h.inr_desc _ _ _
  have hid : ψ ≫ CommRingCat.ofHom φ = 𝟙 _ := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, Category.comp_id]
      ext x; rfl
    · rw [← Category.assoc, h2, Category.comp_id]
      ext r
      change φ (qm (Ideal.Quotient.mk c r)) = χ (Ideal.Quotient.mk c r)
      rw [← hw']
      rfl
  have hφsurj : Function.Surjective φ := fun e =>
    ⟨ψ e, by
      have := congrArg (fun g => g.hom e) hid
      simpa using this⟩
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨y, hy⟩ := hφsurj e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  · refine le_antisymm ?_ hle
    intro x hx
    have hx1 : ψ.hom (π x) = q x := by
      rw [← CommRingCat.hom_ofHom q, ← h1]; rfl
    rw [RingHom.mem_ker] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q x = 0
    rw [← hx1, hx, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

namespace GlobalTheory.Glue

variable {T : Scheme.{0}} {F G : T.Modules}

theorem le_iSup_affine (U : T.Opens) :
    U ≤ ⨆ k : {W : T.Opens // IsAffineOpen W ∧ W ≤ U}, k.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hxW⟩

variable (j : ∀ V : T.Opens, IsAffineOpen V → Γ(F, V) →ₗ[Γ(T, V)] Γ(G, V))
  (hj : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s : Γ(F, V)), j V' hV' (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (j V hV s))


include hj in
theorem agree {U W W' V : T.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWU : W ≤ U)
    (hW'U : W' ≤ U) (h₁ : V ≤ W) (h₂ : V ≤ W') (s : Γ(F, U)) :
    GlobalTheory.Twist.resM G h₁ (j W hW (GlobalTheory.Twist.resM F hWU s)) =
      GlobalTheory.Twist.resM G h₂ (j W' hW' (GlobalTheory.Twist.resM F hW'U s)) := by
  refine GlobalTheory.Twist.sec_ext_of_cover (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ V} => k.1)
    (fun k => k.2.2) (le_iSup_affine V) fun k => ?_
  rw [GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM, ← hj _ _ hW k.2.1, ← hj _ _ hW' k.2.1,
    GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM]

include hj in
theorem exists_glue (U : T.Opens) (s : Γ(F, U)) :
    ∃ t : Γ(G, U), ∀ (W : T.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U),
      GlobalTheory.Twist.resM G hWU t = j W hW (GlobalTheory.Twist.resM F hWU s) := by
  obtain ⟨t, ht⟩ := GlobalTheory.Twist.exists_sec_of_cover
    (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ U} => k.1) (fun k => k.2.2) (le_iSup_affine U)
    (fun k => j k.1 k.2.1 (GlobalTheory.Twist.resM F k.2.2 s))
    fun k l => agree j hj k.2.1 l.2.1 k.2.2 l.2.2 _ _ s
  exact ⟨t, fun W hW hWU => ht ⟨W, hW, hWU⟩⟩

def glue (U : T.Opens) (s : Γ(F, U)) : Γ(G, U) := Classical.choose (exists_glue j hj U s)


end GlobalTheory.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBounds
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.QuoShape

theorem antitone_of_adj {N : ℕ} (f : Fin N → ℤ) (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  have hab' : a ≤ b := hab
  clear hab
  induction b, hab' using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega))

theorem shape {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hH : W.Hyp) (hD : W.IsDiv) (n : ℕ)
    (hn : 4 * (W.T : ℤ) * n ≤ W.h0) :
    (∀ τ, Antitone (W.u1 τ)) ∧
    (∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b) ∧
    ∀ τ a, |(W.u1 τ a : ℝ)| ≤ W.b / 2 := by
  have hT : (4 : ℤ) ≤ W.T := by have := hH.h1; omega
  have bar : ∀ τ (a b : Fin N), (a : ℕ) + 1 = W.p → (b : ℕ) = W.p → (n : ℤ) + 1 ≤ W.u1 τ a - W.u1 τ b := by
    intro τ a b ha hb
    have h := ((GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b (by omega)).2.1 hb).2
    have h2 : (n : ℤ) ≤ W.u1 τ a - W.u1 τ b - 3 * N := le_of_mul_le_mul_left (hn.trans h) (by omega)
    have h3 := b.isLt
    omega
  refine ⟨fun τ => antitone_of_adj _ fun a b hab => ?_, bar, fun τ a => ?_⟩
  · by_cases hb : (b : ℕ) = W.p
    · have := bar τ a b (by omega) hb
      omega
    · have := (GlobalTheory.MeanTop.divided_gaps ι N W hH hD τ a b hab).1 hb
      omega
  · have h1 := (GlobalTheory.MeanTop.divided_entries ι N W hH hD τ a).1
    have h2 : 4 * |W.u1 τ a| ≤ |W.u τ a| + W.c0 + 4 * N :=
      (mul_le_mul_of_nonneg_right (by omega) (abs_nonneg _)).trans h1
    have h3 : 4 * |(W.u1 τ a : ℝ)| ≤ |(W.u τ a : ℝ)| + W.c0 + 4 * N := by exact_mod_cast h2
    have h4 := hH.h5 τ a
    linarith

theorem ranks_le (D : D7) : 80 * D.R.f * D.R.r ^ 2 ≤ D.R.r * D.R.f ^ 2 * D.R.m ^ 2 * D.R.k * (D.R.f * D.R.r.choose 2) := by
  have hf := SizeTZ.two_le_f D
  have hr := SizeTZ.six_le_r D
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  generalize D.R.f = f at *
  generalize D.R.r = r at *
  generalize D.R.m = m at *
  generalize D.R.k = k at *
  have hc : r ≤ r.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
    exact Nat.mul_le_mul_left _ (by omega)
  calc 80 * f * r ^ 2 = r * 2 ^ 2 * 2 ^ 2 * 5 * (f * r) := by ring
    _ ≤ r * f ^ 2 * m ^ 2 * k * (f * r.choose 2) := by gcongr

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem shape_at {PP : ℝ} (hPP : 1 ≤ PP) (hW : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m) (u1 : Psi p.T.Q.H → Fin ((dat p i).p + (dat p i).q) → ℤ)
    (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (dat p i).p + (dat p i).q = D.R.r ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p →
      (nCol (dat p i) : ℤ) + 1 ≤ u1 τ a - u1 τ b) ∧ ∀ τ a, |(u1 τ a : ℝ)| ≤ 2 * L.sc.b := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hW.hyp hi
  have hH1 := hH u1
  have hcol : (nCol (dat p i) : ℝ) ≤ 20 * D.R.f * (D.R.r : ℝ) ^ 2 :=
    SizeTZ.nCol_le_of_pins p.fw.laws.pins ⟨Nat.le_add_left _ _, i.2⟩
  have hr : (80 : ℝ) * D.R.f * (D.R.r : ℝ) ^ 2 ≤
      D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ) := by
    rw [hW.dim]; exact_mod_cast ranks_le D
  have hn : 4 * ((lenT p i PP : ℕ) : ℤ) * (nCol (dat p i) : ℕ) ≤ h0 := by
    have hT0 : (0 : ℝ) ≤ lenT p i PP := Nat.cast_nonneg _
    have h1 : 4 * (lenT p i PP : ℝ) * (nCol (dat p i) : ℝ) ≤ h0 := by
      refine le_trans ?_ hh
      generalize (lenT p i PP : ℝ) = T at *
      calc 4 * T * (nCol (dat p i) : ℝ) ≤ 4 * T * (20 * D.R.f * (D.R.r : ℝ) ^ 2) := by gcongr
        _ = 1 * (T * (80 * D.R.f * (D.R.r : ℝ) ^ 2)) := by ring
        _ ≤ PP * (T * (D.R.r * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (GlobalTheory.CompHt.dimFlag (dat p i) : ℝ))) := by gcongr
        _ = _ := by ring
    exact_mod_cast h1
  obtain ⟨a1, a2, a3⟩ := shape (wtsAt p i PP h0 S eta u1) hH1 ((quo_iff p i PP h0 S eta u1).1 hq) (nCol (dat p i)) hn
  have b1 : D.R.k - 1 < (dat p i).p := hH1.kc_lt
  have b2 : (dat p i).p < (dat p i).p + (dat p i).q := hH1.p_lt
  refine ⟨by omega, by omega, hW.sig.2.2, a1, a2, fun τ a => (a3 τ a).trans (le_of_eq ?_)⟩
  show 4 * L.sc.b / 2 = 2 * L.sc.b
  ring

end GlobalTheory.RefSum.QuoShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem fnOf_app_of_pff : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (m : Y ⟶ X) (φ : X.functionField →+* Y.functionField), PFF (𝟙 _) m φ → ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ m ⁻¹ᵁ V) (a : Γ(X, V)), fnOf (m ⁻¹ᵁ V) hV' ((m.app V).hom a) = φ (fnOf V hV a) := by
  intro X Y _ _ m φ hφ V hV hV' a
  have h : gp Y ≫ m = spMap φ ≫ gp X := by
    obtain ⟨l, h1, h2⟩ := hφ
    rw [Category.comp_id] at h1
    rw [← h1, h2]
  have hloc : IsLocalHom φ := inferInstance
  have e1 : Spec.map (m.stalkMap (genericPoint Y)) ≫ X.fromSpecStalk (m (genericPoint Y)) =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) := by
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]; exact h
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of Y.functionField)).symm.injective
    (a₁ := ⟨m (genericPoint Y), m.stalkMap (genericPoint Y), inferInstance⟩)
    (a₂ := ⟨genericPoint X, CommRingCat.ofHom φ, hloc⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e1)
  obtain ⟨h₁, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only at e3
  have key : X.presheaf.germ V _ hV' ≫ m.stalkMap (genericPoint Y) =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ := by
    rw [e3, TopCat.Presheaf.stalkCongr_hom]
    exact X.presheaf.germ_stalkSpecializes_assoc hV' _ _
  have key' : m.app V ≫ Y.presheaf.germ (m ⁻¹ᵁ V) (genericPoint Y) hV' =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ :=
    (Scheme.Hom.germ_stalkMap m V (genericPoint Y) hV').symm.trans key
  exact congrArg (fun q => CommRingCat.Hom.hom q a) key'

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericPrincipal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericAmpleDvr

theorem triv_theta {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) :=
  CubeNoeth.triv_of_faces allSixLaws.1.globalFns hA hL (thφ A (x3 A)) thε
    (fun r i b h => AbLaw.CubeGen.trivAt_of_formal hL r (AbLaw.CubeGen.prod_face r i b h))
    (fun r b h => AbLaw.CubeGen.prod_face r 0 b h)

end GlobalTheory.GenericAmpleDvr
end

