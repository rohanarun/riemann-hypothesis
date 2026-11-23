module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransExpAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3057
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpandsFScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierGluingLocalTuples
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorsionPointsEqSameValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.TorsUniq

theorem same_point : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b ∧ ∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ x fr g g₂ w w₂ hw₀ hfr hg hw ho hg₂ hw₂ ho₂
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨e, -⟩ := GlobalTheory.Poinc.Sep.LiesUniq.eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hn g g₂ w w₂ x fr hg hg₂ hw hw₂ hfr ho ho₂
  subst e
  exact ⟨rfl, fun _ _ _ _ => rfl⟩

end GlobalTheory.GSep.TorsUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorusCharacterUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.GSep.TorCharUnique


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem equiv_of_qkToAkU {R : Type} [CommRing R] [IsDomain R] {J : Ideal R} (hB : AdmBase R J) {D : DegData R J}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif J D A G) {k : ℕ} (hk : 1 ≤ k) (p p' : QkPt D.toPre (FractionRing R) k)
    (x : TFK (R := R) (FractionRing R) ⟶ A.A) (h : QkToAkU U.toUnifPre (FractionRing R) k p x)
    (h' : QkToAkU U.toUnifPre (FractionRing R) k p' x) : QkPt.Equiv D.toPre (FractionRing R) p p' := by
  have hL : Laws := _root_.GlobalTheory.abelianSchemeLaws_all.1
  let F := AlgebraicClosure (FractionRing R)
  have hf : (algebraMap (FractionRing R) F).comp (algebraMap (FractionRing R) (FractionRing R)) =
      algebraMap (FractionRing R) F := RingHom.ext fun _ => rfl
  refine (GlobalTheory.ArcExt.equiv_qkExt_iff (algebraMap (FractionRing R) F) hf D.tau_bimult p p').1 ?_
  refine GlobalTheory.TorsionMapInj.qkToAk_injective_closed R J hB D A G hG U F k hk _ _
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ?_ ?_
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p _).2 rfl) x).1 h
  · exact (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.globalFns hL.kerPow U hk
      ((GlobalTheory.TorusExt.qkExt_iff D.tau_bimult _ hf p' _).2 rfl) x).1 h'



attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem torChar_unique : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (τ : X₁.S.Gam) (χ χ' : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ → GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ' → χ = χ' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 τ χ χ' h h'
  obtain ⟨p, x, hy, hg, hq, hx⟩ := h.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ))
  obtain ⟨p', x', hy', hg', hq', hx'⟩ := h'.2 _ ((isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ'))
  obtain rfl : x = x' := by
    apply Over.OverMorphism.ext
    refine 𝔪.cart.1.hom_ext (hx.trans hx'.symm) ?_
    rw [Over.w, Over.w]
  have hB : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (lt_of_lt_of_le two_pos X₁.S.N_ge)
  obtain ⟨z, hz, he⟩ := (GlobalTheory.TorusExt.equiv_iff 𝔪.D.tau_bimult _ _).1
    (equiv_of_qkToAkU hB 𝔪.semi 𝔪.U hn p p' x hq hq')
  rw [hy, hy', zero_add] at hz
  have hz0 : z = 0 := by
    have : ((X₁.S.r * X₁.S.N : ℕ) : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hz.symm
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast (by omega))
  rw [hz0, map_zero, add_zero, hg, hg'] at he
  exact (Additive.ofMul.injective (GlobalTheory.TorusExt.torusPt_injective he)).symm

end GlobalTheory.GSep.TorCharUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesSharpReferenceSixteenTerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_iso_exists : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) := by
  intro g l hl hodd W hW
  have LL := GlobalTheory.abelianSchemeLaws_all
  choose J hJ Mat κ w w' hTf using _root_.GlobalTheory.Poinc.Sep.sharp_fibre_theta_object W hW
  have hD := fun gQ : ℕ => @_root_.GlobalTheory.ZM.descend_to_theta_field LL.1 LL.2 (8 * gQ) (J gQ) (hJ gQ) (Mat gQ) (κ gQ) l (w gQ) (w' gQ) hl hodd
  choose j₀f hj₀f using hD
  refine ⟨(Finset.range (g + 1)).sup j₀f + 1, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hS C u mo hmo hTh K _ _ ev k₀ hk₀ hrat σ hσ
  have hj1 : 1 ≤ j := by omega
  obtain ⟨bT, t, v, ψ, hSh, hPr, hHT, hψ, hL, htor⟩ :=
    hTf Q.g l hl hodd j hj1 V V₁ hCN hlu Q rfl ρ hρ D e hS C u mo hmo hTh K ev k₀ hk₀ hrat
  have hle : j₀f Q.g ≤ j := by
    have := Finset.le_sup (f := j₀f) (Finset.mem_range.2 (by omega : Q.g < g + 1))
    omega
  have hs : spMap k₀.subtype = spMap k₀.subtype ≫ spMap (RingHom.id k₀) := by
    simp [spMap]
  obtain ⟨t₀, ⟨φ, hφ, hLφ, hpts, -⟩, -⟩ :=
    hj₀f Q.g j hle k₀ bT k₀ K (RingHom.id k₀) k₀.subtype (spMap k₀.subtype) t v hs hSh hPr hHT
  have hσe : σ.toRingHom.comp k₀.subtype = k₀.subtype := RingHom.ext fun r => hσ r r.2
  obtain ⟨f, hf, hfL, hfq⟩ := GlobalTheory.Poinc.Sep.Twist.twist_fibre_iso V₁ D.P.A D.P.L D.P.isLB K ev σ k₀ k₀.subtype hσe t.A t.L t.isLB ψ hψ hL t₀.A t₀.L t₀.isLB φ hφ hLφ
  refine ⟨f, hf, hfL, ?_⟩
  intro y hy q hq1 hq2
  obtain ⟨k, hk⟩ := hy
  obtain ⟨y', hy'1, hy'2⟩ := _root_.GlobalTheory.TorsionTransfer.torsion_transfer V₁ D.P.A K ev t.A ψ hψ k₀ k₀.subtype t₀.A φ hφ (l ^ k) y hk q hq1 hq2
  haveI : IsAlgClosed k₀ := hk₀
  have hlk : IsUnit ((l ^ k : ℕ) : k₀) := by
    have h1 : IsUnit (ev (l : V₁)) := hlu.map ev
    have h2 : IsUnit ((l : k₀) : K) := by simpa using h1
    have h3 : IsUnit (l : k₀) := by
      rcases h2.exists_left_inv with ⟨x, hx⟩
      exact isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx
    simpa using h3.pow k
  obtain ⟨y₀, hy₀⟩ := _root_.GlobalTheory.TorsRat.torsion_point_rational k₀ K k₀.subtype t₀.A t₀.ab (l ^ k) hlk y' hy'1
  rw [hfq q y₀ (by rw [← hy'2, hy₀]) hq2, hq1]

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTranslationExponentsAffine
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

theorem trans_exp_affine : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩) :=
  GlobalTheory.Poinc.Sep.TransAff.transExp_affine

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTermCoefficientSqEqMonomialSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.Coef

theorem ev_units_zpow {V K : Type} [CommRing V] [Field K] (f : V →+* K) (v : Vˣ) (n : ℤ) :
    f ((v ^ n : Vˣ) : V) = f v ^ n := by
  have h1 : f ((v ^ n : Vˣ) : V) = ((Units.map f.toMonoidHom (v ^ n) : Kˣ) : K) := rfl
  rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem coef_sq_mem_monomial : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 = ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) ^ 2 = r * ∏ k, ev (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
  intro N₁ hN V₁ _ _ _ hV hunit D hpe htb X C _ e u mo hmo hT K _ _ ev k₀ hk₀ τ₀ m N s ε hs hτ hmo2 W₀ _ ib hB hib mu c
  obtain ⟨θ, b, t, χt, s₀, G, hθ, hb, ht, hχt, hs₀, hG, hGf⟩ :=
    _root_.GlobalTheory.Poinc.Sep.CoefInt.integral_sq_terms N₁ hN V₁ hV hunit D hpe htb X C e u mo hmo hT τ₀ m N s ε hs hτ hmo2
  obtain ⟨Λ, hΛ⟩ := _root_.GlobalTheory.USep.EvG.ev_values N₁ hN V₁ hV hunit D X C e τ₀ θ hθ b hb t ht χt hχt G hGf K ev k₀ hk₀ W₀ ib hB hib
  obtain ⟨-, -, -, -, -, -, -, -, -, c₀, hc₀⟩ := hT
  have hc₀' : u 0 c₀ * mo 0 = 1 := hc₀
  have hm0 : mo 0 ^ 2 = 1 := by
    have h := hmo2 0
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one] at h
    exact IsFractionRing.injective V₁ (FractionRing V₁) (by simpa using h)
  have hu0 : u 0 c₀ ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hc₀'
    simpa only [mul_pow, hm0, _root_.mul_one, one_pow] using h
  have hP0 : ((∏ k, (hs k).unit ^ ε (.inr k) (e 0) (e 0) : V₁ˣ) : V₁) = 1 := by
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one, Units.val_one]
  have h0 : s₀ = G 0 c₀ := by
    have h := hG 0 c₀
    rw [hu0, _root_.one_mul, hP0, _root_.one_mul] at h
    exact h
  obtain ⟨r₀, hr₀, e₀⟩ := hΛ 0 c₀
  obtain ⟨r, hr, e₁⟩ := hΛ mu c
  have hev0 : ev s₀ ≠ 0 := (hs₀.map ev).ne_zero
  have hΛr₀ : Λ * r₀ ≠ 0 := by rw [← e₀, ← h0]; exact hev0
  have hr₀0 : r₀ ≠ 0 := right_ne_zero_of_mul hΛr₀
  have hΛ0 : Λ ≠ 0 := left_ne_zero_of_mul hΛr₀
  refine ⟨r / r₀, k₀.div_mem hr hr₀, ?_⟩
  have h := congrArg ev (hG mu c)
  rw [map_mul, map_mul, map_pow, e₁, h0, e₀, Units.coe_prod, map_prod] at h
  simp only [ev_units_zpow, IsUnit.unit_spec] at h
  field_simp
  apply mul_left_cancel₀ hΛ0
  linear_combination h

end GlobalTheory.USep.Coef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFramesScaleByConstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFrameScale

section General

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange GlobalTheory.ExpFieldCompare

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_expandsF_scale_pow (w w' : IndefiniteRowSideFullHecke.BaseChangeCharts.Ident U) : ∃ d : F, d ≠ 0 ∧
    ∀ (k : ℕ) t s, U.ExpandsF F k w'.1 t s → U.ExpandsF F k w.1 t (d ^ k • s) := by
  obtain ⟨u, hu⟩ := exists_isoVal_ratio A.isLB U.LG.isLB w'.2 w.2
  obtain ⟨c₀, hc₀, huc⟩ := BoxExpansion.unit_const globalFns_holds A U.gen u
  refine ⟨algebraMap (FractionRing R) F c₀, (map_ne_zero _).2 hc₀, fun k t s h => ?_⟩
  obtain ⟨v, h₁, h₂⟩ := h
  have z : U.ExpandsG F k (0 : GroupSec U F k) 0 := (expandsG_iff U F k _ _).2
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, (Fin.sum_univ_zero _).symm,
      fun α => (map_zero _).trans (Fin.sum_univ_zero _).symm⟩
  have h₃ := expandsG_lin U F k (algebraMap (FractionRing R) F c₀ ^ k) h₂ z
  rw [add_zero, add_zero] at h₃
  refine ⟨_, ?_, h₃⟩
  refine (isoRelM_iff w.1 (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t _).2 fun y a b ha hb => ?_
  have e := (isoRelM_iff w'.1 (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t v).1 h₁ _ (𝟙 _) y a b ha hb
  have e₃ : (𝟙 _ ≫ prGK G F) ≫ ((Over.pullback (jK R)).obj G).hom =
      ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) ≫ jFK (R := R) F := by
    simp only [Category.id_comp]
    exact (isPullback_groupBase F).w
  have e₄ : (gm (𝟙 _ ≫ prGK G F) y ⊤ u).val = BoxExpansion.constHomVal ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) y
      (algebraMap (FractionRing R) F c₀) :=
    ((gs_unit (𝟙 _ ≫ prGK G F) y ⊤ trivial u).symm.trans
      (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
        ((constVal_specMap _ _ y c₀).trans (BoxExpansion.constVal_eq _ _ _))))
  refine (powVal_smul (π := groupBase G F) _ v (𝟙 _ ≫ 𝟙 _) y (i := a) ha).trans ?_
  rw [e, hu _ (𝟙 _ ≫ prGK G F) y a b ha hb, mul_zpow, Units.val_mul, BoxExpansion.constVal_eq, map_pow, ← e₄,
    zpow_natCast (gm _ _ _ _), Units.val_pow_eq_pow_val, _root_.mul_assoc]

end General

theorem frames_scale : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ w₀₂ : W0 𝔪.U.toUnifPre), w₀.IsGen → w₀₂.IsGen →
  ∃ u : FractionRing V, u ≠ 0 ∧ ∀ (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s : Fam 𝔪.D.toPre (FractionRing V) k),
    𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀₂ th (u ^ k • s) := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ w₀₂ h₀ h₂
  obtain ⟨d, hd, H⟩ := exists_expandsF_scale_pow 𝔪.U.toUnifPre (FractionRing V) ⟨w₀₂, h₂⟩ ⟨w₀, h₀⟩
  exact ⟨d, hd, fun k th s h => H k th s h⟩

end GlobalTheory.GenFrameScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryExistsNormalModelEffCartierAlongTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_zhModel_effCartier_orders : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsProjOver X₁.M.s → ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ hproj
  obtain ⟨ι, K, hK, Jk, hJ, t, hι, ht, hloc⟩ := _root_.GlobalTheory.UPoinc.exists_uLocTuples_theta E H Dw hpq φ hφ l Xo c C X₁
  obtain ⟨Y, πY, U₀, EE, out, hhom, hprop, hAdm, hEE, hdiv⟩ :=
    GlobalTheory.Poinc.exists_admissible_projective_theta_model X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big X₁.M hproj K Jk t ht
  obtain ⟨D, hDU, hDord⟩ := _root_.GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples E H Dw hpq φ hφ l Xo c C X₁ ι K Jk t ht Y U₀ EE out hAdm hdiv
    (hloc Y U₀ EE out hAdm hEE)
  have hsupp := _root_.GlobalTheory.UPoinc.SuppTrait.support_not_mem_range E H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hhom ι D hDU hDord
  exact ⟨ι, Y, πY, D, hι, hhom, hprop, hAdm.1.normal, hsupp,
    _root_.GlobalTheory.UPoinc.AllTraits.orders_all E H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hEE hhom ι D hsupp hDord⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingGaloisTransportDeeperLevel
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem uGalTransport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, (∀ x, a (D.lab x) = D.lab x) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs
  obtain ⟨a, hG, hfix⟩ := _root_.GlobalTheory.UPoinc.UGalAct.exists_galLab E H Dw hpq l Xo cf C X₁ D σ
  exact ⟨a, hfix, fun p _ z₁ ct y h h' yy hL =>
    _root_.GlobalTheory.UPoinc.UGalTrans.isLab_conj E H Dw hpq l Xo cf C X₁ D σ s hs a hG hfix p z₁ ct y h h' yy hL⟩

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_cohomology_bijective : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective_of_aic) | (exact GlobalTheory.EtC.gmPhi_bijective_of_aic) | (intros; apply GlobalTheory.EtC.gmPhi_bijective_of_aic  <;> assumption)
end

