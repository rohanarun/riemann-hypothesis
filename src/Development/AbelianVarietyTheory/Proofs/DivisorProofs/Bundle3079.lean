module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModuliObjectSpreadNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartDescendsOfThetaTermsRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem descAt_of_thetaTerms : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  intro g n hn hodd
  obtain ⟨j₁, h₁⟩ := _root_.GlobalTheory.USep.DescentBaseChange.polarised_part_model g n hn hodd
  obtain ⟨j₂, h₂⟩ := _root_.GlobalTheory.USep.points_defOver g n hn hodd
  refine ⟨max j₁ j₂, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨B₀, iG₀, iC₀, M₀, B', iG', π₁, π₀, w, hA, hM, hp1, hp0, hw⟩ :=
    h₁ j (le_trans (le_max_left _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
  have hP := h₂ j (le_trans (le_max_right _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
    B₀ M₀ B' π₁ π₀ w hA hM hp1 hp0 hw
  have hsq : ∀ a : D.X, (spMap ev ≫ (D.c a).left) ≫ D.P.A.hom = 𝟙 (Sp K) ≫ spMap ev := by
    intro a
    rw [Category.assoc, Over.w (D.c a)]
    simp
  let c' : D.X → (Sp K ⟶ B'.left) := fun a => hp1.1.lift (spMap ev ≫ (D.c a).left) (𝟙 _) (hsq a)
  have hc1 : ∀ a, c' a ≫ B'.hom = 𝟙 _ := fun a => hp1.1.lift_snd _ _ _
  have hc2 : ∀ a, c' a ≫ π₁ = spMap ev ≫ (D.c a).left := fun a => hp1.1.lift_fst _ _ _
  choose c₀ hc₀ using fun a => hP a (c' a) (hc1 a) (hc2 a)
  exact ⟨B₀, iG₀, iC₀, M₀, c₀, B', iG', π₁, π₀, w, c', hA, hM, hp1, hp0, hw, fun a => ⟨hc1 a, hc2 a, (hc₀ a).symm⟩⟩

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMapEq
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.CharpolyAV

section Rho

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
  {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X)

def rho : End A →+ Module.End (WittVector p k) (T.M G) :=
  AddMonoidHom.mk' (fun g => T.map (t.map t g.asHom.hom)) fun g h => by
    have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    haveI : IsMonHom (g.asHom.hom * h.asHom.hom) := inferInstanceAs (IsMonHom (g + h).asHom.hom)
    show T.map (t.map t (g.asHom.hom * h.asHom.hom)) = _
    rw [TorsionTower.map_mul]
    exact hfun.2.2.1 _ _

theorem rho_apply (g : End A) : rho T t g = T.map (t.map t g.asHom.hom) := rfl

theorem rho_pow (f : End A) (n : ℕ) : rho T t (f ^ n) = rho T t f ^ n := by
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, rho_apply]
    show T.map (t.map t (𝟙 A.X)) = _
    rw [TorsionTower.map_id]
    exact hfun.1
  | succ n ih =>
    rw [pow_succ, pow_succ', ← ih, rho_apply, rho_apply, rho_apply]
    show T.map (t.map t (f.asHom.hom ≫ (f ^ n).asHom.hom)) = _
    rw [TorsionTower.map_comp t t t]
    exact hfun.2.1 _ _

theorem rho_aeval (f : End A) (R : Polynomial ℤ) :
    rho T t (Polynomial.aeval f R) = Polynomial.aeval (rho T t f) R := by
  induction R using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, eq_intCast (algebraMap ℤ (End A)),
      eq_intCast (algebraMap ℤ (Module.End (WittVector p k) (T.M G))), ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul, rho_pow]

end Rho

theorem charpoly_map_eq : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)] (f : End A),
    (T.map (t.map t f.asHom.hom)).charpoly = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom (WittVector p k)) := by
  intro p _ T k _ _ _ A G t _ _ f
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  have hFc : ∀ (g : End A) (x : T.M G), T.map (t.map t g.asHom.hom) (T.F G x) = T.F G (T.map (t.map t g.asHom.hom) x) :=
    fun g x => hfun.2.2.2.2.2.2.1 _ x
  have hFinj : Function.Injective (T.F G) := (_root_.GlobalTheory.Dieu.theory_V_verschiebung p T k G).1
  let ψ : ℤ_[p] →+* WittVector p k :=
    (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
    have hu : IsUnit (ψ (PadicInt.unitCoeff hx0 : ℤ_[p])) := (Units.isUnit _).map ψ
    have hpn : ((p : WittVector p k)) ^ x.valuation ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p k)
    exact hpn ((hu.mul_right_eq_zero).1 hx)
  have hrank : Module.finrank (WittVector p k) (T.M G) = 2 * A.dim :=
    hfun.2.2.2.2.2.2.2.1.trans ((_root_.GlobalTheory.AVTower.exists_tower_and_height_eq p k A).2 G t)
  obtain ⟨P, hPm, hP⟩ := _root_.GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly p k (T.M G) (T.F G) ψ (T.map (t.map t f.asHom.hom)) hFinj (hFc f)
  obtain ⟨⟨hQm, hQdeg, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k A f
  have hPdeg : P.natDegree = 2 * A.dim := by
    rw [← hPm.natDegree_map ψ, hP, LinearMap.charpoly_natDegree, hrank]
  have key : P.map (algebraMap ℤ_[p] ℚ_[p]) = (charpoly f).map (Int.castRingHom ℚ_[p]) := by
    refine _root_.GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq p _ _ (hPm.map _) (hQm.map _) ?_ ?_
    · rw [hPm.natDegree_map, hQm.natDegree_map, hPdeg, hQdeg]
    · intro R
      obtain ⟨PR, -, hPR⟩ := _root_.GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly p k (T.M G) (T.F G) ψ
        (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) hFinj (hFc _)
      set d : ℤ_[p] := (-1) ^ Module.finrank (WittVector p k) (T.M G) * PR.coeff 0 with hd_def
      have hd : LinearMap.det (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) = ψ d := by
        rw [LinearMap.det_eq_sign_charpoly_coeff, ← hPR, Polynomial.coeff_map, hd_def, map_mul, map_pow,
          map_neg, map_one]
      have habs := GlobalTheory.Dieu.AbsDet.norm_det_eq_norm_deg p T k A G t ψ (Polynomial.aeval f R) d hd
      have hd' : LinearMap.det (Polynomial.aeval (T.map (t.map t f.asHom.hom)) R) = ψ d := by
        rw [← hd]; exact congrArg LinearMap.det (rho_aeval T t f R).symm
      rw [_root_.GlobalTheory.prod_aeval_aroots_padic_eq_det p (WittVector p k) (T.M G) ψ _ P R d hψ hP hd']
      have hQ : (charpoly f).map (Int.castRingHom ℚ_[p]) =
          ((charpoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
        rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
      have h2 := GlobalTheory.T.deg_aeval_end_eq_prod_aroots k A f (PadicAlgCl p) R
      rw [hQ, Polynomial.aroots_map]
      erw [← h2]
      rw [PadicAlgCl.norm_extends, map_natCast, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
      rw [PadicInt.padic_norm_e_of_padicInt, habs]
      rw [← PadicInt.padic_norm_e_of_padicInt]; push_cast; rfl
  have hP' : P = (charpoly f).map (Int.castRingHom ℤ_[p]) := by
    apply Polynomial.map_injective (algebraMap ℤ_[p] ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])
    rw [key, Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
  rw [← hP, hP', Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _

end GlobalTheory.Dieu.CharpolyAV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitsFourierTermsAllLevels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.isNoetherianRing_stalk {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (z₁ : X₁.M.Z) : IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  have := X₁.M.lft
  have : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  infer_instance

theorem four_of_classical : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), PosW W → (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → Φ.Four W (X₁.S.r * X₁.S.N) := by
  intro g n F W Z i X₁ p _ z₁ Φ hW h y₀ N₀
  obtain ⟨N, hN, hd, k, Q, t, B, _, _, _, _, _, 𝔷, hinj, hfix, hmax, hk, hu, ht, hc⟩ :=
    GlobalTheory.T.thetaFourier_classSums_deeper_finite_extension g n F W Z i X₁ p z₁ Φ h y₀ (N₀ + 1)
  have := X₁.normal.isDomain_stalk z₁
  have := X₁.normal.isIntegrallyClosed_stalk z₁
  have := X₁.isNoetherianRing_stalk z₁
  have hu' : ∀ y, @IsUnimodMod ℤ _ (Φ.X y₀) (Φ.X y) _ (Φ.mod y₀) _ (Φ.mod y) N (k y) := fun y => by
    convert hu y <;> exact Subsingleton.elim _ _
  exact ⟨N, by omega, hd, k, Q, t, hk, hu', ht,
    OrbTrace.orbitSums_of_classSums ℤ id g p _ Φ 8 W _ N y₀ k Q t B hinj hfix 𝔷 hmax (by omega) hW hu' hc⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifiedOnOpenOfSpecialisesToClassified
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ClsOpen

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.ClsOpen


open GlobalTheory.ClsOpen in
theorem GlobalTheory.clsOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (D' : Datum H) (L : LowBase D' c) (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base R → GlobalTheory.Mum.Base V → ∀ (C : Fam Xo c V) (t₁ : SAB H (Sp R)) (P₁ : PELUnif (maximalIdeal R) t₁) (iw : L.W →+* R) (θ : R →+* V), IsLocalHom θ → θ.comp (iw.comp L.b) = C.b → ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → R) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ L.D.X) (e₁ : P₁.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ i, θ (s (.inl i)) ≠ 0) → (∀ j, IsUnit (s (.inr j))) → DivFrom L P₁.D.toPre P₁.oD iw s ε e₁ → DivFrom L C.P.D.toPre C.P.oD (θ.comp iw) (fun k => θ (s k)) ε e → ∃ (y₁ : Sp (FractionRing R) ⟶ Xo.XF c) (yo : Sp (Localization.Away (∏ i, s (.inl i))) ⟶ Xo.XF c) (κ : Sp (FractionRing V) ⟶ Sp (Localization.Away (∏ i, s (.inl i)))), y₁ ≫ pullback.snd _ _ = jK R ≫ spMap (iw.comp L.b) ∧ GlobalTheory.UPoinc.GenOf Xo c y₁ t₁ ∧ (∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, s (.inl i))), g ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK R → g ≫ yo = y₁) ∧ κ ≫ spMap (algebraMap R (Localization.Away (∏ i, s (.inl i)))) = jK V ≫ spMap θ ∧ κ ≫ yo = C.y := by
  intro E _ _ _ H Dw l Xo c φ D' L R V _ _ _ _ _ _ hR hV C t₁ P₁ iw θ hθ hb m N s ε e₁ e hε hs hu hD₁ hD
  set f : R := ∏ i, s (.inl i) with hf_def
  have hθf : θ f ≠ 0 := by rw [hf_def, map_prod]; exact Finset.prod_ne_zero_iff.2 fun i _ => hs i
  have hf0 : f ≠ 0 := fun h => hθf (by rw [h, map_zero])
  have hsk : ∀ k, s k ≠ 0 := by
    rintro (i | j)
    · exact fun h => hs i (by rw [h, map_zero])
    · exact (hu j).ne_zero
  have hθk : ∀ k, θ (s k) ≠ 0 := by
    rintro (i | j)
    · exact hs i
    · exact ((hu j).map θ).ne_zero
  let A := Localization.Away f
  have hpow : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf0
  haveI : IsDomain A := IsLocalization.isDomain_localization hpow
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (Submonoid.powers f) A hR.1.1
  haveI : IsIntegrallyClosed R := hR.1.2.2.1
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A (Submonoid.powers f) hpow
  have hψ := GlobalTheory.T.psiUnitOn_basicOpen_of_comesFromBase L P₁.D.toPre P₁.oD iw s ε e₁ hD₁ f (by
    rintro (i | j)
    · exact ⟨1, by rw [pow_one, hf_def]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)⟩
    · exact ⟨0, (hu j).dvd⟩)
  obtain ⟨tO, ⟨mO⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap (algebraMap R A)) t₁
  obtain ⟨hpr, ham, hkt⟩ := _root_.GlobalTheory.UCanon.Principal.isProper_relAmple_kTriv_of_psiUnitOn R hR t₁ P₁ f hψ tO mO
  have htors : GlobalTheory.TChart.TorsRat tO.G l.M' :=
    (GlobalTheory.TorsAway.torsRat_away_iff R f t₁.G tO.G mO.φ mO.cart l.M').1 (_root_.GlobalTheory.UCanon.torsRat_of_divFrom L R hR t₁ P₁ iw s ε e₁ hε hsk hD₁)
  let K := FractionRing V
  have hunitK : IsUnit (((algebraMap V K).comp θ) f) := by
    rw [RingHom.comp_apply]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hθf)
  let g : A →+* K := IsLocalization.Away.lift f hunitK
  have hg : g.comp (algebraMap R A) = (algebraMap V K).comp θ := IsLocalization.lift_comp _
  let bA : c.F →+* A := (algebraMap R A).comp (iw.comp L.b)
  let incl := (IntermediateField.inclusion c.le).toRingHom
  have hgb : g.comp bA = (algebraMap V K).comp C.b := by
    show g.comp ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [← RingHom.comp_assoc, hg, RingHom.comp_assoc, hb]
  have E1 : spMap g ≫ spMap (algebraMap R A) = jK V ≫ spMap θ :=
    (spMap_comp' _ _).symm.trans ((congrArg spMap hg).trans (spMap_comp' _ _))
  obtain ⟨oK, ⟨mK⟩⟩ := GlobalTheory.LevelQuotRep.obj_pull_same Xo.univ (C.y ≫ pullback.fst _ _)
  have hsK : (C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap g ≫ spMap (bA.comp incl) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, C.y_over, spMap_comp' incl bA, ← Category.assoc,
      ← spMap_comp' bA g, hgb, spMap_comp']
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := (genOf_iff Xo c C.y C.t).1 C.gen
  obtain ⟨bc⟩ := _root_.GlobalTheory.UCanon.sabMap_of_same_coords L R V hR hV t₁ P₁ C.t C.P iw θ hθ s ε e₁ e hθk hD₁ hD
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.cancel (Category.id_comp _) m₂ mK.toSABMap
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl bc m₁
  obtain ⟨n₃⟩ := GlobalTheory.TraitOrder.comp (Category.id_comp _) n₂ n₁
  obtain ⟨n₄⟩ := GlobalTheory.TraitOrder.cancel E1 mO n₃
  obtain ⟨o, ho, ⟨mo⟩⟩ := _root_.GlobalTheory.ObjSpread.exists_obj Dw l c A bA tO hpr ham hkt htors K g _ oK hsK n₄
  obtain ⟨f₀, ⟨hf₀s, ⟨mf₀⟩⟩, -⟩ := Xo.rep (Sp A) (spMap (bA.comp incl)) inferInstance o
  have hf₀ : f₀ ≫ Xo.s = spMap bA ≫ spMap incl := by rw [hf₀s, spMap_comp']
  let yo : Sp A ⟶ Xo.XF c := pullback.lift f₀ (spMap bA) hf₀
  have hκ : spMap g ≫ yo = C.y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      obtain ⟨mk'⟩ := GlobalTheory.LevelQuotRep.obj_comp mo mf₀
      exact (Xo.rep (Sp K) _ inferInstance oK).unique ⟨by rw [Category.assoc, hf₀s, hsK], ⟨mk'⟩⟩ ⟨rfl, ⟨mK⟩⟩
    · rw [Category.assoc, pullback.lift_snd, C.y_over, ← spMap_comp', hgb, spMap_comp']
  have hunitR : IsUnit ((algebraMap R (FractionRing R)) f) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf0)
  let jA : A →+* FractionRing R := IsLocalization.Away.lift f hunitR
  have hjA : jA.comp (algebraMap R A) = algebraMap R (FractionRing R) := IsLocalization.lift_comp _
  have hg₀ : spMap jA ≫ spMap (algebraMap R A) = jK R := by rw [← spMap_comp', hjA]
  have mo' : SABMap tO Xo.univ.t f₀ := ho ▸ mf₀.toSABMap
  refine ⟨spMap jA ≫ yo, yo, spMap g, ?_, ?_, ?_, E1, hκ⟩
  · rw [Category.assoc, pullback.lift_snd, ← hg₀, Category.assoc]
    show spMap jA ≫ spMap ((algebraMap R A).comp (iw.comp L.b)) = _
    rw [spMap_comp']
  · refine (genOf_iff Xo c _ t₁).2 ?_
    obtain ⟨t', ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap jA) tO
    exact ⟨t', GlobalTheory.TraitOrder.comp hg₀ mO n,
      GlobalTheory.TraitOrder.comp (by rw [Category.assoc, pullback.lift_fst]) mo' n⟩
  · intro g' hg'
    obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
    have h2 : CommRingCat.ofHom (algebraMap R A) ≫ φ' = CommRingCat.ofHom (algebraMap R (FractionRing R)) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact hg')
    have h3 : φ'.hom = jA := IsLocalization.ringHom_ext (Submonoid.powers f)
      ((congrArg CommRingCat.Hom.hom h2).trans hjA.symm)
    have h4 : φ' = CommRingCat.ofHom jA := by ext1; exact h3
    rw [h4]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegeneratingFamilyDataFromBaseAlgClosedResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.VData

theorem exists_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → IsAlgClosed (ResidueField V) → ∀ (C : MonoFam Xo c φ V), Nontrivial C.P.D.toPre.X → ∃ (D' : Datum H) (L : LowBase D' c) (θ₀ : L.W →+* V) (N : ℕ) (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar L.D.X)) (e : C.P.D.toPre.X ≃ₗ[𝓞 E] L.D.X) (s : Fin C.m ⊕ Fin N → V), D'.p + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.p ∧ D'.q + Module.finrank (𝓞 E) C.P.D.toPre.X = Dw.q ∧ IsLocalHom θ₀ ∧ θ₀.comp L.b = C.b ∧ (∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X)) ∧ (∀ i, Associated (s (.inl i)) (C.s i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ DivFrom L C.P.D.toPre C.P.oD θ₀ s (fun k => (ε k : LinearMap.BilinForm ℤ L.D.X)) e := by
  intro E _ _ _ H Dw l Xo c φ V _ _ _ hV hk C hX
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  haveI : Module.Finite (𝓞 E) C.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hr : 1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X := Module.finrank_pos
  obtain ⟨Z, D', f, o', φB, -, -, -, hp, hq, hpb, hact, hw, -⟩ := GlobalTheory.LowDat.exists_lower Xo c V hV C.toFam hr
  have hrk := C.rank
  haveI : IsMonHom (Iso.refl C.P.D.toPre.P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨i, hi, hiφ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl C.P.D.toPre.P.A)) hpb
  have hiφ' : i.hom.left ≫ φB = 𝟙 _ := hiφ
  have hia : ∀ a : 𝓞 E, (letI := H.starRing; C.P.oD.onB.act a) ≫ i.hom = i.hom ≫ o'.t.act.act a := by
    intro a
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hiφ', hact, ← Category.assoc, hiφ',
        Category.comp_id, Category.id_comp]
    · rw [Over.w, Over.w]
  have hM : IsUnit ((l.M' : ℕ) : V) := by
    have h1 : IsUnit ((l.M' : ℕ) : c.F) := IsUnit.mk0 _ (Nat.cast_ne_zero.2 (level_pos l).ne')
    simpa using h1.map C.b
  obtain ⟨x', hx₁, hx₂, hx₃⟩ := _root_.GlobalTheory.AbDivLocal.exists_divided_linear V hV.1.2.2.2 hk o'.t.G
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩ (𝓞 E) o'.t.act
    C.P.D.toPre.X (fun y => C.P.D.toPre.c y ≫ i.hom)
    (fun y z => by
      rw [C.P.D.toPre.c_add, ← MonObj.mul_comp]; rfl)
    (fun a y => by
      letI := H.starRing
      rw [C.P.oD.c_lin, Category.assoc, hia, Category.assoc]) l.M' hM
  obtain ⟨L, θ₀, e, m, hθ, hb, hc⟩ := _root_.GlobalTheory.UCanon.lowBase_of_linearPoints D' c V C.b o' C.P.D.toPre.X x' hx₁ hx₂
  obtain ⟨N, b, hbas⟩ := C.cone.basis
  let ε := b.map (pullBalEquiv H.bar e).symm
  have hε : ∀ i, C.δ i = pull e.toLinearMap (ε (.inl i) : LinearMap.BilinForm ℤ L.D.X) := fun j => by
    have h1 : pullBalEquiv H.bar e (ε (.inl j)) = ⟨C.δ j, C.cone.mem j⟩ := by
      simp [ε, hbas]
    exact (congrArg Subtype.val h1).symm
  have hPL := C.P.D.toPre.P.isLB
  have l₁ : LBIso C.P.D.toPre.P.L (o'.t.PP.L.pull i.hom.left) :=
    LBIso.trans hPL (pull_isLB hPL _) (pull_isLB o'.t.PP.isLB _)
      ((GlobalTheory.PolBaseChange.lbIso_refl hPL).chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl))
      (GenSpread.lbIso_pull_of_lbIso hw i.hom.left hiφ'.symm).symm
  have l₂ : LBIso o'.t.PP.L (L.o.t.PP.L.pull m.toSABMap.φ) := m.lin.imp fun _ h => h.1
  have l₃ : LBIso o'.t.PP.L (L.D.P.L.pull (m.toSABMap.φ ≫ L.φB)) :=
    LBIso.trans o'.t.PP.isLB (pull_isLB L.o.t.PP.isLB _) (pull_isLB L.D.P.isLB _) l₂ (GenSpread.lbIso_pull_of_lbIso L.ab.2.2 _ rfl)
  obtain ⟨s, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_periods_monomialFamily_coords_over_base Xo c φ V hV hk C D' L θ₀ e (i.hom.left ≫ m.toSABMap.φ ≫ L.φB)
    (((isGrpPullback_of_iso i).comp (m.cart.comp L.ab.1)).congr (by simp) rfl)
    (fun a => by
      have h1 := congrArg (·.left) (hia a)
      simp only [Over.comp_left] at h1
      rw [← Category.assoc, h1, Category.assoc, ← Category.assoc _ m.toSABMap.φ, m.act, Category.assoc, L.ab.2.1]
      simp only [Category.assoc])
    (LBIso.trans hPL (pull_isLB o'.t.PP.isLB _) (pull_isLB L.D.P.isLB _) l₁ (GenSpread.lbIso_pull_of_lbIso l₃ _ rfl))
    (fun y => by
      rw [← map_nsmul, ← hc, hx₃, Over.comp_left, Category.assoc]) N ε hε
  exact ⟨D', L, θ₀, N, ε, e, s, by omega, by omega, hθ, hb, hε, h₁, h₂, h₃⟩

end GlobalTheory.VData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smoothOfRelDim_of_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S))) : SmoothOfRelativeDimension g X.hom := by
  have e : X.hom = inv (pullback.fst X.hom (𝟙 S)) ≫ pullback.snd X.hom (𝟙 S) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (inv (pullback.fst X.hom (𝟙 S))) (pullback.snd X.hom (𝟙 S))
  simpa using this

theorem smoothOfRelDim_pullback_snd_identity {S : Scheme.{0}} (X : Over S) (g : ℕ)
    (h : SmoothOfRelativeDimension g X.hom) : SmoothOfRelativeDimension g (pullback.snd X.hom (𝟙 S)) := by
  have e : pullback.snd X.hom (𝟙 S) = pullback.fst X.hom (𝟙 S) ≫ X.hom := by
    rw [pullback.condition, Category.comp_id]
  rw [e]
  have := smoothOfRelativeDimension_comp (n := 0) (m := g) (pullback.fst X.hom (𝟙 S)) X.hom
  simpa using this

theorem dualAbelianScheme : GlobalTheory.Published.DualAbelianScheme := by
  intro S A _ hA
  obtain ⟨B, _, P, hB, hdim, hdual⟩ := _root_.GlobalTheory.DualExist.exists_dual S A hA
  refine ⟨B, inferInstance, P, hB, fun g hg => ?_, hdual, _root_.GlobalTheory.BidualAbelian.isDual_swap S A B P hA hB hdim hdual⟩
  exact smoothOfRelDim_of_pullback_snd_identity B g (hdim g S (𝟙 S) (smoothOfRelDim_pullback_snd_identity A g hg))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentBundlePowerHeckeQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_bundle_power_hecke_quotient' : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∃ P₀ : LB (G2 A').left, P₀.IsLB ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient) | (exact GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelKilledCharOfTorusLabel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.TorLabel

theorem exists_torus_char : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) :=
  fun I X₁ z₁ act V _ _ _ ev X _ t δ 𝔪 => GlobalTheory.T.exists_torus_char_of_label_orthogonal_dividing I X₁ z₁ act V ev X t δ 𝔪

end GlobalTheory.GSep.TorLabel
end

