module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.ega_holds : GlobalTheory.LN.Ega :=
  _root_.GlobalTheory.LN.ega_of_laws _root_.GlobalTheory.allSixLaws.1 _root_.GlobalTheory.allSixLaws.2.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleHasHeckeQuotientNoetherianDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkLoc

theorem range_subset_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {N n : ℕ}
    {σ : Fin n → (𝟙_ (Over S) ⟶ G)} {K : Set G.left} (h : Lists N σ K) {k : Type} [Field k] (x : Sp k ⟶ S)
    (z : Over.mk x ⟶ G) : Set.range z.left ⊆ K ↔ ∃ j, z = toUnit _ ≫ σ j := by
  obtain ⟨-, rfl, -⟩ := h
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hz ⟨q, rfl⟩)
    have h1 := ListedSubgroup.eq_comp_section G.hom (σ j).left (Over.w (σ j)) _ q hj
    rw [Over.w z] at h1
    exact ⟨j, Over.OverMorphism.ext h1⟩
  · rintro ⟨j, rfl⟩ _ ⟨y, rfl⟩
    exact Set.mem_iUnion.2 ⟨j, x y, (Scheme.Hom.comp_apply x (σ j).left y).symm⟩

theorem isUnit_natCast {F R : Type} [Field F] [CharZero F] [CommRing R] (s : Sp R ⟶ Sp F) (m : ℕ) (hm : 0 < m) :
    IsUnit (m : R) := by
  have h : IsUnit (m : F) := (Nat.cast_ne_zero.2 hm.ne').isUnit
  simpa using h.map (Spec.preimage s).hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

noncomputable abbrev pol {S : Scheme.{0}} {s : S ⟶ Sp (KA l)} (o : Ob D l s) : Out.PolAV S :=
  have h := GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ S s o
  { A := o.t.G, isAb := h.1, g := Module.finrank ℚ E / 2 * (D.p + D.q), smoothDim := h.2.1, L := o.t.PP.L,
    isLB := o.t.PP.isLB, rigid := h.2.2.1, sym := h.2.2.2, ample := o.ample, ktriv := o.ktriv }

theorem weilIs_one {S : Scheme.{0}} [ConnectedSpace S] {s : S ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)}
    {p i n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)} {K : Set o.t.G.left} (hp : 0 < p)
    (hu : IsUnit ((p ^ 2 : ℕ) : Γ(S, ⊤))) (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (j j' : Fin n) :
    Out.WeilIs o.t.G o.t.PP.L ((p ^ 2 : ℕ) : ℤ) (σ j) (σ j') 1 := by
  have := o.proper
  obtain ⟨U, hU, hW⟩ := GlobalTheory.exists_clopen_weilIs_iff GlobalTheory.firstFiveLaws.1 S (pol o) (p ^ 2) (𝟙_ (Over S)) (σ j) (σ j') 1
    (pow_pos hp 2) hu (hL.1 j) (hL.1 j') (one_pow _)
  obtain ⟨s₀⟩ : Nonempty S := inferInstance
  let k : Type := AlgebraicClosure (S.residueField s₀)
  let x : Sp k ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s₀) k)) ≫ S.fromSpecResidueField s₀
  obtain ⟨C, hC, hk⟩ := hH k x
  obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
  have hmem : ∀ j, toUnit (Over.mk x) ≫ σ j ∈ C := fun j =>
    (hC _).2 ((range_subset_iff hL x _).2 ⟨j, rfl⟩)
  have h₁ := (hW (Over.mk x) (toUnit _)).1 (by
    rw [map_one, Nat.cast_pow]
    exact hk.2.2.2.1 _ (hmem j) _ (hmem j'))
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  have hc : IsClopen (U : Set (𝟙_ (Over S)).left) := ⟨hU, U.isOpen⟩
  have h₂ : (U : Set (𝟙_ (Over S)).left) = Set.univ := hc.eq_univ ⟨_, h₁ ⟨q, rfl⟩⟩
  have h₃ := (hW (𝟙_ (Over S)) (𝟙 _)).2 (by rw [h₂]; exact Set.subset_univ _)
  rw [map_one, Category.id_comp, Category.id_comp] at h₃
  exact h₃

theorem hasQuot_of_linearisation {R : Type} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {s : Sp R ⟶ Sp (KA l)} (o : Ob D l s) {𝔓 : Ideal (𝓞 E)} {p i n : ℕ}
    {σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)} {K : Set o.t.G.left} (hD : 1 ≤ D.p + D.q) (hA : admitted l 𝔓 p)
    (hL : Lists (p ^ 2) σ K) (hH : HeckeSet D o.t 𝔓 p i K) (C : Type) [CommGroup C] [Finite C]
    (v : C →* (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (e : C → Fin n) (he : Function.Injective e) (hv : ∀ c, v c = σ (e c))
    (hσ : ∀ j, ∃ c, v c = σ j)
    (hu : ∃ u : ∀ c : C, LB.Gen (LB.LinComb (lbPow o.t.PP.L (p ^ 2)) (K := Fin 2)
        ![𝟙 o.t.G.left, ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left] ![1, -1]), (∀ c, (u c).IsGen) ∧
      ∀ c c', LB.Gen.Corr (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u (c * c')) (LB.mulGen (lbPow o.t.PP.L (p ^ 2)) _ _ _ _ (u c)
        (LB.pullGen (lbPow o.t.PP.L (p ^ 2)) _ _ (u c') ((toUnit o.t.G ≫ v c) * 𝟙 o.t.G).left))) :
    HasQuot o p K := by
  have := o.proper
  obtain ⟨u, hu₁, hu₂⟩ := hu
  have hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (c : C),
      toUnit (Over.mk t) ≫ v c = 1 → c = 1 := fun k _ _ t c h => by
    have h₁ : toUnit (Over.mk t) ≫ v c = toUnit (Over.mk t) ≫ v 1 := by rw [h, map_one, MonObj.comp_one]
    rw [hv, hv] at h₁
    exact he (hL.2.2 k t (congrArg CommaMorphism.left h₁))
  obtain ⟨B, gB, ψ, hB, hψ, hf, het, hs, hk₁, hk₂⟩ : ∃ (B : Over (Sp R)) (_ : GrpObj B) (ψ : o.t.G ⟶ B),
      IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ c, v c ≫ ψ = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (x : Over.mk t ⟶ o.t.G),
        x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ v c :=
    GlobalTheory.exists_quotient_by_finite_group_of_sections R (pol o) C v hinj
  obtain ⟨M, hM, hiso⟩ := GlobalTheory.LinDescent.exists_descent (Sp R) o.t.G B ψ C v (lbPow o.t.PP.L (p ^ 2))
    (LB.isLB_linComb o.t.PP.isLB _ _) hψ hf het hs hk₁ (fun k _ _ t => ⟨hk₂ k t, hinj k t⟩) u hu₁ hu₂
  have hker : KerSet ψ K := fun k _ _ t z => by
    rw [hk₂, range_subset_iff hL]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨e c, by rw [hv]⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨c, hc⟩ := hσ j
      exact ⟨c, by rw [hc]⟩
  obtain ⟨t', ψ', h₁, h₂, h₃, h₄, h₅⟩ := _root_.GlobalTheory.HkFam.exists_quotient_triple_family E H R o.t _ p B ψ M (isUnit_natCast s) hA.2.2.1.pos o.proper
    (pol o).smoothDim o.ample o.ktriv hB hM hψ hf het hs (fun k _ _ x => by
      obtain ⟨C₀, hC₀, hk⟩ := hH k x
      have hm : ∀ z : Over.mk x ⟶ o.t.G, z ≫ ψ = 1 ↔ z ∈ C₀ := fun z => (hker k x z).trans (hC₀ z).symm
      refine ⟨(Nat.card_congr (Equiv.subtypeEquivRight hm)).trans hk.2.2.2.2.1, fun z hz => ⟨?_, fun a => ?_⟩⟩
      · obtain ⟨c, rfl⟩ := (hk₂ k x z).1 hz
        rw [← MonObj.comp_pow, hv, hL.1, MonObj.comp_one]
      · exact (hm _).2 (hk.1 z ((hm z).1 hz) a)) hiso
  exact GlobalTheory.hasQuot_of_isIsogT E H D l 𝔓 p i (Sp R) s o t' ψ' K hD hA h₁ h₂ h₃ h₄
    (fun k _ _ x z => (h₅ _ z).trans (hker k x z)) hH

end GlobalTheory.HkLoc


open GlobalTheory.HkLoc in
theorem GlobalTheory.exists_etale_hasQuot_of_lists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] (s : Sp R ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over (Sp R)) ⟶ o.t.G)) (K : Set o.t.G.left) (q : Sp R), 1 ≤ D.p + D.q → admitted l 𝔓 p → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → ∃ (R' : Type) (_ : CommRing R') (π : Sp R' ⟶ Sp R) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π), Etale π ∧ q ∈ Set.range π ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l 𝔓 p i n R _ _ _ s o σ K q hD hA hL hH
  have hp : 0 < p := hA.2.2.1.pos
  have hΓ : ∀ m : ℕ, 0 < m → IsUnit (m : Γ(Sp R, ⊤)) := fun m hm => by
    simpa using (isUnit_natCast s m hm).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  obtain ⟨C, hC⟩ := GlobalTheory.HkFam.exists_subgroup_eq_range_of_lists E H D 𝔓 p i n (Sp R) o.t σ K o.proper (hΓ p hp) hL hH
  have hmem : ∀ c : C, ∃ j, σ j = c := fun c => by
    have : c.1 ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G)) := c.2
    rwa [hC] at this
  choose e he using hmem
  have einj : Function.Injective e := fun c c' h => Subtype.ext (by rw [← he, h, he])
  have : Finite C := Finite.of_injective e einj
  obtain ⟨R', _, _, het, hq, hlin⟩ := GlobalTheory.exists_etale_linearisation R (pol o) (p ^ 2) C C.subtype q
    (isUnit_natCast s _ (pow_pos hp 2)) (pow_pos hp 2)
    (fun c => Subtype.ext (by
      have := hL.1 (e c)
      rw [he] at this
      exact this))
    (fun c c' => by
      have := weilIs_one o hp (hΓ _ (pow_pos hp 2)) hL hH (e c) (e c')
      rw [he, he] at this
      exact this)
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have hπ : Etale π := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.2 het
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  have : AlgebraicGeometry.IsReduced (Sp R') := GlobalTheory.isReduced_of_smooth_of_isReduced π
  have : _root_.IsReduced R' := (affine_isReduced_iff (CommRingCat.of R')).1 this
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨h₁, -, h₂⟩ := (GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t o'.t π m.toSABMap o.proper).2 K
  obtain ⟨σ', hσ', hL'⟩ := h₂ _ _ σ hL
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over (Sp R')))
  have tu : (toUnit (Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ π))).left = π := by simp
  let v : C →* (𝟙_ (Over (Sp R')) ⟶ o'.t.G) := MonoidHom.mk' (fun c => ρ.symm (toUnit _ ≫ c.1)) fun c c' => by
    rw [← map_mul, ← MonObj.comp_mul]
    rfl
  have hv : ∀ c, (v c).left ≫ m.toSABMap.φ = π ≫ c.1.left := fun c => by
    change (ρ.symm (toUnit _ ≫ c.1)).left ≫ _ = _
    rw [← e₀, ρ.apply_symm_apply, Over.comp_left, tu]
  have hv' : ∀ (c : C) j, σ j = c → v c = σ' j := fun c j h =>
    Over.OverMorphism.ext (m.cart.1.hom_ext (by rw [hv, hσ', h]) ((Over.w _).trans (Over.w _).symm))
  refine ⟨R', inferInstance, π, o', m, hπ, hq, hasQuot_of_linearisation o' hD hA hL' (h₁ hH) C v e einj
    (fun c => hv' c _ (he c)) (fun j => ⟨⟨σ j, ?_⟩, hv' _ j rfl⟩) ?_⟩
  · change σ j ∈ (C : Set (𝟙_ (Over (Sp R)) ⟶ o.t.G))
    rw [hC]
    exact ⟨j, rfl⟩
  · exact hlin o'.t.G m.toSABMap.φ o'.t.PP.L v m.cart o'.t.PP.isLB (m.lin.imp fun _ h => h.1) hv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelListsModuloPermutations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkPerm

theorem lists_perm {S : Scheme.{0}} {G : Over S} [GrpObj G] {N n : ℕ} {σ : Fin n → (𝟙_ (Over S) ⟶ G)}
    {K : Set G.left} (h : Lists N σ K) (g : Equiv.Perm (Fin n)) : Lists N (fun j => σ (g j)) K := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨fun j => h₁ _, ?_, fun k _ _ x => (h₃ k x).comp g.injective⟩
  rw [h₂]
  exact (g.surjective.iUnion_comp (fun j => Set.range (σ j).left)).symm

theorem exists_perm {α : Type} {n : ℕ} {u v : Fin n → α} (hu : Function.Injective u) (hv : Function.Injective v)
    (h : Set.range u = Set.range v) : ∃ g : Equiv.Perm (Fin n), ∀ j, u (g j) = v j := by
  have : ∀ j, ∃ i, u i = v j := fun j => by
    have : v j ∈ Set.range u := h ▸ Set.mem_range_self j
    exact this
  choose g hg using this
  have gi : Function.Injective g := fun a b e => hv (by rw [← hg, ← hg, e])
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 gi), hg⟩

theorem exists_lists_mod_perm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ), admitted l 𝔓 p → ∃ (Y Hk : Scheme.{0}) (q : Y ⟶ Hk) (π₁ : Hk ⟶ Xo.X) (oY : Ob D l ((q ≫ π₁) ≫ Xo.s)) (m : ObjMap oY Xo.univ (q ≫ π₁)) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite q ∧ Etale q ∧ Surjective q ∧ IsFinite π₁ ∧ Etale π₁ ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ Y), y ≫ q = y' ≫ q ↔ Set.range (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ) = Set.range (fun j => y' ≫ (σ j).left ≫ m.toSABMap.φ) ∧ y ≫ q ≫ π₁ = y' ≫ q ≫ π₁) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ Xo.X) (t : SAB H T) (mu : SABMap t Xo.univ.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃ h : T ⟶ Y, h ≫ q ≫ π₁ = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  intro E _ _ _ H D l Xo P p i n hA
  obtain ⟨Y, a, oY, m, σ, K, fa, ea, hL, hK, hu⟩ := _root_.GlobalTheory.exists_finiteEtale_heckeLists E H D l P p i n Xo.X Xo.s Xo.univ hA
  have hρ := fun g : Equiv.Perm (Fin n) => hu Y a oY.t m.toSABMap (fun j => σ (g j)) K (lists_perm hL g) hK
  choose ρ hρ₁ hρ₂ using hρ
  have r₁ : ∀ g, ρ g ≫ a = a := fun g => (hρ₁ g).1
  have r₂ : ∀ g j, ρ g ≫ (σ j).left ≫ m.toSABMap.φ = (σ (g j)).left ≫ m.toSABMap.φ := fun g => (hρ₁ g).2
  have one : ρ 1 = 𝟙 Y := (hρ₂ 1 _ ⟨by simp, fun j => by simp⟩).symm
  have mul : ∀ g c, ρ (g * c) = ρ g ≫ ρ c := fun g c =>
    (hρ₂ (g * c) _ ⟨by rw [Category.assoc, r₁, r₁], fun j => by
      rw [Category.assoc, r₂, r₂]; rfl⟩).symm
  have inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y),
      Function.Injective fun j => y ≫ (σ j).left ≫ m.toSABMap.φ := by
    intro k _ _ y b c e
    apply hL.2.2 k y
    have w : ∀ j, (σ j).left ≫ oY.t.G.hom = 𝟙 Y := fun j => Over.w _
    refine m.toSABMap.cart.1.hom_ext ?_ ?_
    · simpa only [Category.assoc] using e
    · simp only [Category.assoc, w]
  have free : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (g : Equiv.Perm (Fin n)), y ≫ ρ g = y → g = 1 := by
    intro k _ _ y g e
    ext1 j
    apply inj k y
    change y ≫ (σ (g j)).left ≫ m.toSABMap.φ = y ≫ (σ j).left ≫ m.toSABMap.φ
    rw [← r₂, ← Category.assoc, e]
  have uq : ∀ (T : Scheme.{0}) (y y' : T ⟶ Y), y ≫ a = y' ≫ a →
      (∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = y' ≫ (σ j).left ≫ m.toSABMap.φ) → y = y' := by
    intro T y y' e₁ e₂
    obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull y oY.t
    obtain ⟨mu, hmu⟩ := GlobalTheory.ObjMaps.exists_sab_comp m.toSABMap m'
    obtain ⟨τ, hτ, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m'.cart K _ n σ hL
    have hτ' : ∀ j, y ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := fun j => by
      rw [hmu, ← Category.assoc, ← hτ, Category.assoc]
    exact (hu T (y ≫ a) _ mu τ _ hL' (GlobalTheory.HkSetPull.heckeSet_pull D P p i m' K hK)).unique ⟨rfl, hτ'⟩
      ⟨e₁.symm, fun j => (e₂ j).symm.trans (hτ' j)⟩
  have hq := GlobalTheory.isQProjOver_comp_of_isFinite_noetherian (KA l) Y Xo.X a Xo.s fa Xo.qproj
  obtain ⟨Hk, q, sH, hs, hG, sep, lft, -⟩ := GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver (KA l) Y (a ≫ Xo.s)
    (Equiv.Perm (Fin n)) ρ hq one mul (fun g => by rw [← Category.assoc, r₁]) free
  have hd := (GlobalTheory.ZM.galoisCover_descent Y Hk q _ ρ hG).1
  obtain ⟨π₁, rfl, -⟩ := hd Xo.X a r₁
  have hs' : π₁ ≫ Xo.s = sH := (hd _ ((q ≫ π₁) ≫ Xo.s) (fun g => by rw [← Category.assoc, r₁])).unique
    (Category.assoc _ _ _).symm hs
  subst hs'
  have : IsSeparated π₁ := IsSeparated.of_comp π₁ Xo.s
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : LocallyOfFiniteType π₁ := locallyOfFiniteType_of_comp π₁ Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨f₁, e₁⟩ := isFinite_and_etale_of_comp_of_finite_etale_cover Y Hk Xo.X q π₁ hG.fin hG.etale hG.onto fa ea
    inferInstance inferInstance
  refine ⟨Y, Hk, q, π₁, oY, m, σ, K, hG.fin, hG.etale, hG.onto, f₁, e₁, hL, hK, fun k _ _ y y' => ⟨fun e => ?_, fun e => ?_⟩,
    fun T f t mu τ K' h₁ h₂ => (hu T f t mu τ K' h₁ h₂).exists⟩
  · obtain ⟨g, rfl, -⟩ := hG.fibre k y y' e
    refine ⟨?_, by rw [← Category.assoc, e, Category.assoc]⟩
    simp only [Category.assoc, r₂]
    exact (g.surjective.range_comp (fun j => y ≫ (σ j).left ≫ m.toSABMap.φ)).symm
  · obtain ⟨g, hg⟩ := exists_perm (inj k y) (inj k y') e.1
    have : y ≫ ρ g = y' := uq _ _ _ (by rw [Category.assoc, r₁]; exact e.2) fun j => by
      rw [Category.assoc, r₂]; exact hg j
    rw [← this, Category.assoc, hG.inv]

end GlobalTheory.HkPerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientClassifyingMapIsogenyUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory

theorem heckeQuot_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left) (f₁ f₂ : S ⟶ Xo.X) (n₁ : ObjMap o₁ Xo.univ f₁) (n₂ : ObjMap o₂ Xo.univ f₂), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → f₁ ≫ Xo.s = s → f₂ ≫ Xo.s = s → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → f₁ = f₂ ∧ ψ₁.left ≫ n₁.toSABMap.φ = ψ₂.left ≫ n₂.toSABMap.φ := by
  intro E _ _ _ H D l Xo P p i S hS s o o₁ o₂ ψ₁ ψ₂ K f₁ f₂ n₁ n₂ hA hK h₁ h₂ i₁ i₂ k₁ k₂
  obtain ⟨-, -, hp, hpP, hM⟩ := hA
  have hnat : ∀ {T : Over S} (x : T ⟶ o.t.G) (n : ℕ), x ≫ o.t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := o.t.act.add 0 0
      rw [add_zero] at h
      have h0 : o.t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, o.t.act.add, MonObj.comp_mul, ih, o.t.act.one, Category.comp_id, pow_succ]
  have hkill : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G),
      Set.range z.left ⊆ K → z ^ p ^ 2 = 1 := by
    intro k _ _ x z hz
    obtain ⟨C, hC, hH⟩ := hK k x
    have hzC := hH.2.2.1 ((hC z).2 hz)
    have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
      rwa [map_natCast] at this
    have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
      rw [Nat.cast_pow, pow_two]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
    rwa [hnat] at h
  obtain ⟨m, hm⟩ := _root_.GlobalTheory.exists_objMap_of_isIsog_of_kerSet E H D l p S s o o₁ o₂ ψ₁ ψ₂ K hp hM i₁ i₂ k₁ k₂ hkill
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2
    f₂ (𝟙 S) n₂).1 m
  have hf : f₁ = 𝟙 S ≫ f₂ :=
    (Xo.rep S s hS o₁).unique ⟨h₁, ⟨n₁⟩⟩ ⟨by rw [Category.id_comp, h₂], ⟨m'⟩⟩
  refine ⟨by rw [hf, Category.id_comp], ?_⟩
  subst hf
  have e := GlobalTheory.obj_rigid_closed GlobalTheory.firstFiveLaws.1 E H D l _ _ _ _ _ _ _ _ Xo.univ o₁ _ (Or.inl hS)
    n₁.toSABMap m'.toSABMap (fun a => ⟨_, n₁.eta a, m'.eta a⟩)
  rw [e, hm', ← Category.assoc, hm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem torsionIso_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso :=
  GlobalTheory.UT.torsionIso_of_pelUnif GlobalTheory.firstFiveLaws
    GlobalTheory.twistBaseChange_and_valuation_statements.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.2

end GlobalTheory.FlatTors
end

