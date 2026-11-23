module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrix
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GramMatrixTwistedLieModels
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientDifferentialMatrixStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_differential_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (P : Matrix (Fin d') (Fin d) k), Q.IsDiff g gB P → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → linQ Qs = P := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.linQ_eq_diff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianQuotientGaugeRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.Flat.FrGauge
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_quotient_gauge_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X) (Q : AbQuot t x) (d d' : ℕ) (g : GermAt t x d) (gB : GermAt Q.tB (𝟙 (Sp k)) d'), ∀ (w : LB.Iso (t.PP.L.pull (pullback.fst t.G.hom x)) (Q.tB.PP.L.pull Q.q.left)), w.IsGen → ∀ Qs : Fin d' → PS k 1 d, (∀ i, MvPowerSeries.constantCoeff (Qs i) = 0) → (∀ m, fibPt t x (g.x m) ≫ Q.q = homAt (𝟙 (Sp k)) (sub1 Qs m) ≫ gB.x m) → ∀ lam : PS k 2 d, (∀ m, ∃ U : (Jet k (Fin 2 × Fin d) m)ˣ, (U : Jet k (Fin 2 × Fin d) m) = psJet m lam ∧ Tr w (cubeF t x ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (cφG t ![jptG t x d g.x m (0 : Fin 2), jptG t x d g.x m (1 : Fin 2)]) (fun I => (homAt (𝟙 (Sp k)) (sub2 Qs m)).left ≫ cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)] I) (cε 2) (g.e m) (LB.pullGen Q.tB.PP.L (cφG Q.tB ![jptG Q.tB (𝟙 (Sp k)) d' gB.x m (0 : Fin 2), jptG Q.tB (𝟙 (Sp k)) d' gB.x m (1 : Fin 2)]) (cε 2) (gB.e m) (homAt (𝟙 (Sp k)) (sub2 Qs m)).left) (unitΓ U⁻¹)) → ∀ (a : 𝓞 E) (wL : AdTy t a) (wB : AdTy Q.tB a), wL.IsGen → wB.IsGen → AdRel t x d g.x g.B.A.act g.B.ad g.e a wL → AdRel Q.tB (𝟙 (Sp k)) d' gB.x gB.B.A.act gB.B.ad gB.e a wB → Tr w (adF t x a) (fun i => sqMap t x ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) i) (fun i => qq Q ≫ Sum.elim (cφG Q.tB ![fst Q.tB.G Q.tB.G, snd Q.tB.G Q.tB.G ≫ Q.tB.act.act (H.bar a)]) (cφG Q.tB ![fst Q.tB.G Q.tB.G ≫ Q.tB.act.act a, snd Q.tB.G Q.tB.G]) i) (Sum.elim (cε 2) fun I => -cε 2 I) (LB.pullGen t.PP.L _ _ wL (sqMap t x)) (LB.pullGen Q.tB.PP.L _ _ wB (qq Q)) 1 → subQ Qs (gB.B.ad a) * ev (n := 2) ![pt k d 0, comp1 (g.B.A.act (H.bar a)) (pt k d 1)] lam = ev (n := 2) ![comp1 (g.B.A.act a) (pt k d 0), pt k d 1] lam * g.B.ad a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | exact GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrGauge.AdRelPf.adRel_series <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebra
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem model_passes_to_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] (A₀ : Over (Sp k)) [GrpObj A₀] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap (algebraMap k V)) φ → ∀ R : Subalgebra k V, ∃ (_ : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R))))) (φ₁ : A.left ⟶ pullback A₀.hom (spMap (algebraMap k R))), IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R)) (pullback.fst _ _) ∧ IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) (spMap R.val.toRingHom) φ₁ ∧ φ₁ ≫ pullback.fst _ _ = φ := by
  intro k V _ _ _ A _ A₀ _ φ h R
  have es : spMap R.val.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k V) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have w : φ ≫ A₀.hom = (A.hom ≫ spMap R.val.toRingHom) ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, es]; exact h.1.w
  let inst : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) :=
    inferInstanceAs (GrpObj ((Over.pullback (spMap (algebraMap k R))).obj A₀))
  have h₁ : IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R))
      (pullback.fst _ _) := isGrpPullback_pullback A₀ (spMap (algebraMap k R))
  have hf : pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  refine ⟨inst, pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w, h₁, ?_, hf⟩
  exact IsGrpPullback.cancel h₁ (h.congr es.symm hf.symm) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockMatrixGramNormal
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

theorem quotNormSq_eq_of_blockFrame : ∀ (N j : ℕ) (hj : j ≤ N) (G G' T : Matrix (Fin N) (Fin N) ℂ) (Γ : Matrix (Fin (N - j)) (Fin (N - j)) ℂ), G.PosDef → G' = Tᴴ * G * T → (∀ a a', T (headIdx hj a) (headIdx hj a') = if a = a' then 1 else 0) → (∀ k a, T (tailIdx hj k) (headIdx hj a) = 0) → (∀ k k', T (tailIdx hj k) (tailIdx hj k') = if k = k' then 1 else 0) → (∀ a k, G' (headIdx hj a) (tailIdx hj k) = 0) → (∀ k k', G' (tailIdx hj k) (tailIdx hj k') = Γ k k') → quotNormSq hj G = Γ.det.re := by
  intro N j hj G G' T Γ hG hG' hT1 hT2 hT3 hG'1 hG'2
  obtain ⟨e, hel, her⟩ : ∃ e : Fin j ⊕ Fin (N - j) ≃ Fin N,
      (∀ a, e (Sum.inl a) = headIdx hj a) ∧ ∀ k, e (Sum.inr k) = tailIdx hj k :=
    ⟨finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hj)),
      fun a => by ext; simp [headIdx],
      fun k => by ext; simp [tailIdx]⟩
  have hhinj : Function.Injective (headIdx hj) := by
    intro a a' h
    rw [← hel, ← hel] at h
    exact Sum.inl_injective (e.injective h)
  have hht : ∀ a k, headIdx hj a ≠ tailIdx hj k := by
    intro a k h
    rw [← hel, ← her] at h
    exact Sum.inl_ne_inr (e.injective h)
  have hblocks : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.submatrix e e =
      Matrix.fromBlocks (M.submatrix (headIdx hj) (headIdx hj))
        (M.submatrix (headIdx hj) (tailIdx hj))
        (M.submatrix (tailIdx hj) (headIdx hj)) (M.submatrix (tailIdx hj) (tailIdx hj)) := by
    intro M
    ext (a | k) (a' | k') <;> simp [hel, her]
  have hdet : ∀ M : Matrix (Fin N) (Fin N) ℂ, M.det = (M.submatrix e e).det := fun M =>
    (Matrix.det_submatrix_equiv_self e M).symm
  have hTdet : T.det = 1 := by
    have h1 : T.submatrix (headIdx hj) (headIdx hj) = 1 := by
      ext a a'; simp [hT1, Matrix.one_apply]
    have h0 : T.submatrix (tailIdx hj) (headIdx hj) = 0 := by
      ext k a; simp [hT2]
    have h2 : T.submatrix (tailIdx hj) (tailIdx hj) = 1 := by
      ext k k'; simp [hT3, Matrix.one_apply]
    rw [hdet T, hblocks T, h1, h0, h2, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hdetG : G'.det = G.det := by
    rw [hG', Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hTdet]
    simp
  have hcol : T.submatrix id (headIdx hj) =
      (1 : Matrix (Fin N) (Fin N) ℂ).submatrix id (headIdx hj) := by
    ext y a'
    obtain ⟨z, rfl⟩ := e.surjective y
    rcases z with a | k
    · simp [hel, hT1, Matrix.one_apply, hhinj.eq_iff]
    · simp [her, hT2, Matrix.one_apply, (hht a' k).symm]
  have key : ∀ M : Matrix (Fin N) (Fin N) ℂ,
      (Mᴴ * G * M).submatrix (headIdx hj) (headIdx hj) =
        (M.submatrix id (headIdx hj))ᴴ * G * M.submatrix id (headIdx hj) := by
    intro M
    first
      | rfl
      | (ext a a'; simp [Matrix.mul_apply, Matrix.conjTranspose_apply])
  have hhh : G'.submatrix (headIdx hj) (headIdx hj) = G.submatrix (headIdx hj) (headIdx hj) := by
    rw [hG', key T, hcol, ← key 1]
    simp
  have hht' : G'.submatrix (headIdx hj) (tailIdx hj) = 0 := by
    ext a k; simp [hG'1]
  have htt : G'.submatrix (tailIdx hj) (tailIdx hj) = Γ := by
    ext k k'; simp [hG'2]
  have hdetblock : G.det = (G.submatrix (headIdx hj) (headIdx hj)).det * Γ.det := by
    rw [← hdetG, hdet G', hblocks G', hht', htt, Matrix.det_fromBlocks_zero₁₂, hhh]
  have hpos : 0 < (G.submatrix (headIdx hj) (headIdx hj)).det :=
    (hG.submatrix hhinj).det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  unfold quotNormSq
  rw [hdetblock, Complex.mul_re, ← him, zero_mul, sub_zero]
  exact mul_div_cancel_left₀ _ hre.ne'

end GlobalTheory.CompanionTheory.Ar.Cusp.BlockFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CodimOneGramTwistAgree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem codim_one_gram_twist_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (t t' : SAB H X) (tp : SAB H (Spec (X.presheaf.stalk p.1))) (m : SABMap tp t (X.fromSpecStalk p.1)) (m' : SABMap (twistSAB tp g) t' (X.fromSpecStalk p.1)) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V), (∀ e, ∃ v : Sp (DualNumber Ω) ⟶ tp.G.left, v ≫ m.φ = (M.pt e).left ∧ v ≫ m'.φ = (M'.pt e).left) → ∀ (z : Sp ℂ ⟶ X), centre z = p.1 → ∀ (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), M.GramAt t.PP.L z b Γ ↔ M'.GramAt t'.PP.L z b Γ :=
  PositivityTheory.UnitarySelfGeneration.gram_matrix_twisted_lie_models

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeFirst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.MuFrame

private theorem isMultiHomog_mul_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a b : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q b) : IsMultiHomog (p * q) (a + b) := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hp m1 h1 k, hq m2 h2 k, Pi.add_apply]

private theorem isMultiHomog_add_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {p q : MvPolynomial ((k : K) × Jt k) ℤ} {a : K → ℕ}
    (hp : IsMultiHomog p a) (hq : IsMultiHomog q a) : IsMultiHomog (p + q) a := by
  classical
  unfold IsMultiHomog at *
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h k
  · exact hq m h k

private theorem isMultiHomog_X_geometry {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] [DecidableEq K]
    (k : K) (i : Jt k) :
    IsMultiHomog (MvPolynomial.X ⟨k, i⟩ : MvPolynomial ((k : K) × Jt k) ℤ) (Pi.single k 1) := by
  classical
  unfold IsMultiHomog
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hk : k' = k
  · subst hk
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  · have hk' : k ≠ k' := Ne.symm hk
    simp [Finsupp.single_apply, hk, hk']

private theorem isMultiHomog_prod_X_one {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    (ch : (k : K) → Jt k) :
    IsMultiHomog (∏ k, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog
      (∏ k ∈ s, (MvPolynomial.X ⟨k, ch k⟩ : MvPolynomial ((k : K) × Jt k) ℤ))
      (∑ k ∈ s, Pi.single k 1) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact isMultiHomog_mul_geometry (isMultiHomog_X_geometry a (ch a)) ih
  have h := key Finset.univ
  convert h using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

private theorem isValueAt_add' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s + s') w (v + v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add_geometry (isMultiHomog_mul_geometry hg hh') ?_,
    isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul_geometry hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, map_add (f := _), hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul, map_add (f := _)]; rw [div_add_div _ _ hw hw']; ring

private theorem isValueAt_mul' {K : Type} {Jt : K → Type} [∀ k, Fintype (Jt k)] {Ω : Type} [Field Ω]
    {y : (k : K) × Jt k → Ω} {w : (k : K) × Jt k → ℂ} {s s' : Ω} {v v' : ℂ}
    (h1 : IsValueAt y s w v) (h2 : IsValueAt y s' w v') : IsValueAt y (s * s') w (v * v') := by
  unfold IsValueAt at *
  obtain ⟨d, g, h, hg, hh, hy, hgs, hw, rfl⟩ := h1
  obtain ⟨d', g', h', hg', hh', hy', hgs', hw', rfl⟩ := h2
  refine ⟨d + d', g * g', h * h', isMultiHomog_mul_geometry hg hg', isMultiHomog_mul_geometry hh hh', ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · simp only [map_mul, hgs, hgs']; ring
  · simp only [map_mul]; exact mul_ne_zero hw hw'
  · simp only [map_mul]; rw [div_mul_div_comm]

private theorem isValueAt_aeval_segreCoord_div {K : Type} [Fintype K] {Jt : K → Type} [∀ k, Fintype (Jt k)]
    {Ω : Type} [Field Ω] (y : (k : K) × Jt k → Ω) (w : (k : K) × Jt k → ℂ) (ch : (k : K) → Jt k)
    (hy : segreCoord y ch ≠ 0) (hw : ∏ k, w ⟨k, ch k⟩ ≠ 0) (P : MvPolynomial ((k : K) → Jt k) ℤ) :
    IsValueAt y (MvPolynomial.aeval (fun c' => segreCoord y c' / segreCoord y ch) P) w
      (MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    unfold IsValueAt
    refine ⟨0, MvPolynomial.C a, 1, isMultiHomog_C_zero a, ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : IsMultiHomog (MvPolynomial.C (1 : ℤ) : MvPolynomial ((k : K) × Jt k) ℤ) 0 :=
        isMultiHomog_C_zero 1
      simpa using h1
    · simp
    · simp
    · simp
    · simp
  | add p q hp hq => simpa only [map_add (f := _)] using isValueAt_add' hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul]
    refine isValueAt_mul' hp ?_
    unfold IsValueAt
    refine ⟨fun _ => 1, ∏ k, MvPolynomial.X ⟨k, i k⟩, ∏ k, MvPolynomial.X ⟨k, ch k⟩,
      isMultiHomog_prod_X_one i, isMultiHomog_prod_X_one ch, ?_, ?_, ?_, ?_⟩
    · simpa [segreCoord] using hy
    · simp only [map_prod, MvPolynomial.aeval_X]
      exact (div_mul_cancel₀ _ hy).symm
    · simpa using hw
    · simp [MvPolynomial.aeval_X]

theorem nonempty_muFrameAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) := by
  classical
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w hco
  unfold CoordsAt at hco
  choose ch hch using hco.1
  have hy : ∀ k, Dc.y ⟨k, ch k⟩ ≠ 0 := fun k => (hco.2 k (ch k) (hch k)).1
  have hwc : ∀ k, w ⟨k, ch k⟩ ≠ 0 := fun k => (hch k).ne_zero
  have hseg : segreCoord Dc.y ch ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hy k)
  have hsegw : ∏ k, w ⟨k, ch k⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hwc k)
  obtain ⟨m, f, cc, hf, hcc, hsum, hfr⟩ := Hd.locally ch hseg
  have hmem : ∀ a, a ∈ chartRing ℤ (segreCoord Dc.y) ch → ∃ P : MvPolynomial ((k : K) → J k) ℤ,
      MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) P = a := by
    intro a ha
    unfold ReciprocityTheory.ChartRestriction.G.Geo.chartRing at ha
    rw [Algebra.adjoin_range_eq_range_aeval] at ha
    obtain ⟨P, hP⟩ := ha
    exact ⟨P, hP⟩
  choose P hP using fun l => hmem (f l) (hf l)
  choose Q hQ using fun l => hmem (cc l) (hcc l)
  have hginj : Function.Injective (genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩) :=
    (CoordTie.gen Or.𝔐.tie).inj _
  have hlift : ∀ q : (k : K) × J k, ∃ t : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ t = Dc.y q / Dc.y ⟨q.1, ch q.1⟩ ∧
      (Scheme.stalkClosedPointTo z).hom t = w q / w ⟨q.1, ch q.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r0, hv, hr0⟩ := (hco.2 k (ch k) (hch k)).2 i
    unfold ValAt at hv
    obtain ⟨hsp, t, ht1, ht2⟩ := hv
    refine ⟨t, ht1, ?_⟩
    rw [ht2, hr0, mul_div_assoc, div_self (hwc k), _root_.mul_one]
  choose t ht1 ht2 using hlift
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Or.𝔐.X.presheaf.stalk (centre z) →+* ℂ,
      ψ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have ht2' : ∀ q, ψ (t q) = w q / w ⟨q.1, ch q.1⟩ := by
    intro q; rw [hψ]; exact ht2 q
  have hval : ∀ R : MvPolynomial ((k : K) → J k) ℤ, ∃ s : Or.𝔐.X.presheaf.stalk (centre z),
      genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s =
        MvPolynomial.aeval (fun c' => segreCoord Dc.y c' / segreCoord Dc.y ch) R ∧
      ψ s =
        MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      refine ⟨((a : ℤ) : Or.𝔐.X.presheaf.stalk (centre z)), ?_, ?_⟩
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
      · rw [map_intCast, MvPolynomial.aeval_C]; exact (eq_intCast _ a).symm
    | add p q hp hq =>
      obtain ⟨s, hs1, hs2⟩ := hp
      obtain ⟨s', hs1', hs2'⟩ := hq
      exact ⟨s + s', by rw [map_add (f := _), map_add (f := _), hs1, hs1'], by rw [map_add (f := _), map_add (f := _), hs2, hs2']⟩
    | mul_X p i hp =>
      obtain ⟨s, hs1, hs2⟩ := hp
      refine ⟨s * ∏ k, t ⟨k, i k⟩, ?_, ?_⟩
      · rw [map_mul, map_prod, hs1, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht1]
        unfold segreCoord
        rw [Finset.prod_div_distrib]
      · rw [map_mul, map_prod, hs2, map_mul, MvPolynomial.aeval_X]
        congr 1
        simp only [ht2']
        rw [Finset.prod_div_distrib]
  obtain ⟨s, hs1, hs2⟩ := hval (∑ l, Q l * P l - 1)
  have hz : genMap Or.𝔐.ξ ⟨centre z, Or.𝔐.all _⟩ s = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs1, map_sub, map_sum, map_one]
    simp only [map_mul, hP, hQ]
    rw [hsum, sub_self]
  have hs0 : s = 0 := hginj (by rw [hz, map_zero])
  have hW : ∑ l, MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (Q l) *
      MvPolynomial.aeval (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) = 1 := by
    have h2 := hs2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs0, map_zero, map_sub, map_sum, map_one] at h2
    simp only [map_mul] at h2
    exact sub_eq_zero.mp h2.symm
  obtain ⟨l0, hl0⟩ : ∃ l, MvPolynomial.aeval
      (fun c' => (∏ k, w ⟨k, c' k⟩) / ∏ k, w ⟨k, ch k⟩) (P l) ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero (fun l _ => by rw [hne l, MulZeroClass.mul_zero])] at hW
    exact zero_ne_one hW
  have hunit : IsUnitAt Dc.y (f l0) w := by
    have hv := isValueAt_aeval_segreCoord_div Dc.y w ch hseg hsegw (P l0)
    rw [hP l0] at hv
    exact Exists.intro _ (And.intro hv hl0)
  obtain ⟨b, hb, u, hu, hΛ⟩ := hfr l0
  exact ⟨MuFrameAt.mk ch (f l0) (And.intro hwc hunit) b hb u hu hΛ⟩

end GlobalTheory.CompanionTheory.Ar.MuFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeSecond
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BlockSumFrame

theorem isVB_comap_of_range {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E'] (A : Lat ξ E')
    (S : Submodule Ω E') (i : E →ₗ[Ω] E') (hinj : Function.Injective i) (hrange : LinearMap.range i = S) {r : ℕ}
    (h : (Lat.comap A S.subtype).IsVB r ⊤) : (Lat.comap A i).IsVB r ⊤ := by
  have hmem : ∀ x, i x ∈ S := fun x => hrange ▸ LinearMap.mem_range_self i x
  let e : E →ₗ[Ω] S := i.codRestrict S hmem
  have hei : ∀ x, ((e x : S) : E') = i x := fun x => rfl
  have he_inj : Function.Injective e := fun x y hxy => hinj (by rw [← hei, ← hei, hxy])
  have he_surj : Function.Surjective e := fun s => by
    have : (s : E') ∈ LinearMap.range i := hrange ▸ s.2
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Subtype.ext hx⟩
  let eq : E ≃ₗ[Ω] S := LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩
  have heq : ∀ x, ((eq x : S) : E') = i x := fun x => rfl
  intro p hp
  obtain ⟨U, hpU, b, hspan, hfr⟩ := h p hp
  refine ⟨U, hpU, fun k => eq.symm (b k), ?_, fun q hq hqU => ?_⟩
  · have : Set.range (fun k => eq.symm (b k)) = eq.symm '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, ← LinearEquiv.coe_coe, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨hli, hst⟩ := hfr q hq hqU
    refine ⟨hli.map' eq.symm.toLinearMap (LinearEquiv.ker _), ?_⟩
    ext x
    have h1 : x ∈ Lat.comap A i q ↔ eq x ∈ Lat.comap A S.subtype q := Iff.rfl
    rw [h1, hst]
    let eR : E ≃ₗ[regAt ξ q] S := eq.restrictScalars (regAt ξ q)
    have hrng : Set.range b = eR '' Set.range (fun k => eq.symm (b k)) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun k => (eq.apply_symm_apply (b k)).symm)
    rw [hrng, ← LinearEquiv.coe_coe, ← Submodule.map_span]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := eR.injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

theorem frame_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (cc : (k : K) → J k) (f : Ω) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z), CoordsAt Or.𝔐.ξ Dc.y z w → IsFrameOver Dc.y (Dc.W τ) cc f b → InFrameDomain Dc.y cc f w → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w τ cc f b h hw hfr hd
  have hT : CoordTie ℤ Or.𝔐.ξ (segreCoord Dc.y) := Or.𝔐.tie
  have hrk : labelRk D (Or.bg τ) + labelRk D (Or.sm τ) = Dc.N := by
    rw [Or.rk_bg, Or.rk_sm]
    exact Nat.add_sub_cancel' Dc.j_le_N
  have hsum := _root_.GlobalTheory.CompanionTheory.Ar.HodgeSum.isVB_sup E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 (Or.bg τ) (Or.sm τ) (Or.bg_ne_sm τ τ)
  rw [hrk] at hsum
  have hvb : (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsVB Dc.N ⊤ :=
    isVB_comap_of_range _ _ (Or.i τ) (Or.i_inj τ) (Or.i_range τ) hsum
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.inChart_unitAt_of_inFrameDomain Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y hT z w cc f h hw hd
  exact (_root_.GlobalTheory.CompanionTheory.Ar.isFrameOver_iff_forall_isFrameAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y (W τ) Dc.N (Dc.W τ) _ hT hvb (Or.lat τ) cc f b hfr.1 hfr.2.1
    hfr.2.2.1).1 hfr _ c1 c2

end GlobalTheory.CompanionTheory.Ar.BlockSumFrame
end
end

