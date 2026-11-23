module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0147
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0232
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0237
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftCocycleMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobSerre
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PreimageMono
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationThetaIntegral
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzFib

theorem inner_jn {D : D7} {n r t : ℕ} (hn : r + t = n) (V : HSp D) (x : Mx D V.rank r) :
    GlobalTheory.StdUnn.inner V (jn hn x (0 : Mx D V.rank t)) (jn hn x (0 : Mx D V.rank t)) =
      bl hn (GlobalTheory.StdUnn.inner V x x) 0 0 0 := by
  set e : Fin n ≃ Fin r ⊕ Fin t := (finSumFinEquiv.trans (finCongr hn)).symm with he
  have hX : jn hn x (0 : Mx D V.rank t) = (Matrix.fromCols x (0 : Mx D V.rank t)).submatrix id e := rfl
  have hadj : adj (jn hn x (0 : Mx D V.rank t)) =
      (Matrix.fromRows (adj x) (0 : Matrix (Fin t) (Fin V.rank) (AE D))).submatrix e id := by
    ext i k
    rw [hX]
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id]
    rcases e i with a | b
    · simp
    · simp
  have hG : (HMul.hMul (gA V) (jn hn x (0 : Mx D V.rank t)) : Mx D V.rank n) =
      (Matrix.fromCols (HMul.hMul (gA V) x : Mx D V.rank r) (0 : Mx D V.rank t)).submatrix id e := by
    ext i j
    rw [hX]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    rcases e j with a | b
    · simp [Matrix.mul_apply]
    · simp
  unfold GlobalTheory.StdUnn.inner
  rw [hG, hadj, ← Matrix.submatrix_mul _ _ e id e Function.bijective_id, Matrix.fromRows_mul_fromCols]
  simp [bl, he]

theorem trace_bl {R : Type} [CommRing R] {n r t : ℕ} (hn : r + t = n) (a : Matrix (Fin r) (Fin r) R)
    (b : Matrix (Fin r) (Fin t) R) (c : Matrix (Fin t) (Fin r) R) (d : Matrix (Fin t) (Fin t) R) :
    Matrix.trace (bl hn a b c d) = Matrix.trace a + Matrix.trace d := by
  unfold bl
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)).symm (fun i => Matrix.fromBlocks a b c d i i),
    Fintype.sum_sum_type]
  simp

theorem trace_nzx {D : D7} {n r t : ℕ} (hn : r + t = n) (V : HSp D) (z : Mx D r r) (x : Mx D V.rank r) :
    Matrix.trace (HMul.hMul (bl hn z 0 (adj (0 : Mx D r t)) 0 : Mx D n n)
        (GlobalTheory.StdUnn.inner V (jn hn x (0 : Mx D V.rank t)) (jn hn x (0 : Mx D V.rank t))) : Mx D n n) =
      Matrix.trace (HMul.hMul z (GlobalTheory.StdUnn.inner V x x) : Mx D r r) := by
  have h0 : adj (0 : Mx D r t) = 0 := by
    ext i j
    simp [adj]
  rw [inner_jn, h0]
  have hm : (HMul.hMul (bl hn z 0 0 0 : Mx D n n) (bl hn (GlobalTheory.StdUnn.inner V x x) 0 0 0) : Mx D n n) =
      bl hn (HMul.hMul z (GlobalTheory.StdUnn.inner V x x) : Mx D r r) 0 0 0 := by
    unfold bl
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  rw [hm, trace_bl]
  simp

theorem conj_char {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (u : AF F) :
    conj (ψ u) = ψ (-u) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]

theorem wz_eq_fib : ∀ {D : D7} {n r t : ℕ} (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D} (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕) {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕) (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib) (Φ : schwartzA θ V.rank n) (g : G D n), Wz M m ψ b₀ (fun g => (ω g Φ).1 0) g = ∫ x, (ω g Φ).1 (jn hn x 0) ∂fib := by
  intro D n r t hP hn M m V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr hμr μt hμt b₀ fib hfib Φ g
  have hPF := hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt
  rw [← (hfib.int _ (hPF (ω g Φ)).2.1).2]
  unfold Wz W
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (ω (M.w * M.nzx z 0 * g) Φ).1 0 * conj (chz ψ b₀ z) = Jt ψ V μr _ z * ψ (-halfTr _)
  have e1 : ω (M.w * M.nzx z 0 * g) Φ = ω M.w (ω (M.nzx z 0) (ω g Φ)) := by
    simp only [map_mul, Module.End.mul_apply]
  rw [e1, (hPF (ω (M.nzx z 0) (ω g Φ))).1]
  unfold chz
  rw [conj_char hψ]
  congr 1
  unfold Jt
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (ω (M.nzx z 0) (ω g Φ)).1 (jn hn x 0) = (ω g Φ).1 (jn hn x 0) * ψ (halfTr _)
  rw [hω.unip _ _ (M.nzx_mat z 0), trace_nzx, mul_comm]

end GlobalTheory.CompanionTheory.WzFib

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneGradedFinite
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.FibGr

section Abs
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem fin_vb [IsNoetherianRing R] {Z : Scheme.{0}} (z : Z ⟶ Spec (CommRingCat.of R)) [IsProper z] (F : C ⥤ ModuleCat.{0} R)
    {ι : Type} [Fintype ι] (U : ι → Z.Opens) (P : ι → ObjectProperty C) (m : ℕ) (hU : (⨆ α, U α) = ⊤)
    (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (V : VB (fun W : Z.Opens => strV z W) U (CrystallineSemistableComparison.Pb.cechH F P m)) (a : ℕ) :
    Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F P m).cx.H a) :=
  vb_fin z U hU ha (CrystallineSemistableComparison.Pb.cechH F P m) V a

theorem fin_zero (F : C ⥤ ModuleCat.{0} R) {ι : Type} (P : ι → ObjectProperty C) (b a : ℕ)
    (h : ∀ i : Fin (a + 1) → ι, Subsingleton (HU F (capT P i) b)) :
    Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F P b).cx.H a) := by
  haveI : Subsingleton ((CrystallineSemistableComparison.Pb.cechH F P b).X a) := ⟨fun x y => funext fun i => (h i).elim _ _⟩
  haveI : Subsingleton ((CrystallineSemistableComparison.Pb.cechH F P b).cx.H a) :=
    ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact congrArg _ (Subtype.ext (Subsingleton.elim _ _))⟩
  infer_instance

end Abs

section Main
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (hI : I = ⊥) {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {γ : DividedPowers I} {p : ℕ}

theorem serre_red [IsNoetherianRing R] (F : Thick (nlFun γ p X q κ) ⥤ ModuleCat.{0} R) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    {ι : Type} (U : ι → X.Opens) (j : ℕ)
    (h : ∀ a b, a + b = j → Module.Finite R ((CrystallineSemistableComparison.Pb.cechH F (fun α => St Q {U α}) b).cx.H a)) :
    Module.Finite R (HU F (St Q (Set.range U)) j) := by
  obtain ⟨𝒮, h𝒮⟩ := serre_fg R
  exact (h𝒮 _).1 (GlobalTheory.CompanionTheory.GlobSt.glob_st.2.1 F Q U 𝒮 j fun a b hab => (h𝒮 _).2 (h a b hab))


include hI in
theorem fin_gen [IsNoetherianRing R] (hp : p ≠ 0) (hn : IsNilpotent (p : R)) [IsProper q] (U : Cov q) (r j : ℕ) :
    Module.Finite R (HU (GF (nlFun γ p X q κ) r) (St ⊤ (Set.range U.U)) j) := by
  refine serre_red (GF (nlFun γ p X q κ) r) ⊤ U.U j fun a b _ => ?_
  by_cases hb : b = r
  · subst hb
    have : IsProper (qF hI q κ) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
    obtain ⟨V⟩ := vb_cech (γ := γ) (p := p) (κ := κ) hI hp hn U b
    have ha : ∀ n (i : Fin (n + 1) → U.ι), IsAffineOpen (capO (fun α => jF hI q κ ⁻¹ᵁ U.U α) i) := fun n i => by
      rw [capO_pre]
      exact aff_pre hI (GlobalTheory.CompanionTheory.GrCech.capO_affine U n i)
    have e : (fun α => St (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) {U.U α}) = fun α => SQ q κ γ p (U.U α) := rfl
    rw [e]
    exact fin_vb (qF hI q κ) _ _ _ b (cover_pre hI U) ha V a
  · refine fin_zero _ _ b a fun i => ?_
    have e := GlobalTheory.CompanionTheory.GrCech.capT_eq (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) U.U i
    obtain ⟨c', -⟩ := _root_.GlobalTheory.CompanionTheory.CoordRes.main (U.c (i 0)) (capO_le U.U i 0) (GlobalTheory.CompanionTheory.GrCech.capO_affine U a i)
    have h := off_at (γ := γ) (p := p) (κ := κ) hI hp hn c' r b hb
    rw [show capT (fun α => St (⊤ : ObjectProperty (Thick (nlFun γ p X q κ))) {U.U α}) i = SQ q κ γ p (capO U.U i) from e]
    exact h

end Main

theorem level_one_gr_finite : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (ρ : O →+* k) (U : Cov q) (r j : ℕ),
    Module.Finite (Wc.Wm l k 1) (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) r) (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((r : ℤ) + 1))) j) := by
  intro l _ k _ _ _ O _ X q _ ρ U r j
  have hI : Wc.Im l k 1 = ⊥ := (Ideal.map_eq_bot_iff_le_ker _).2 (by
    rw [Ideal.mk_ker, pow_one])
  have hl : ((l : ℕ) : Wc.Wm l k 1) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ 1}))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by rw [pow_one]; exact Ideal.mem_span_singleton_self _)
  have hn : IsNilpotent ((l : ℕ) : Wc.Wm l k 1) := by
    rw [hl]
    exact IsNilpotent.zero
  haveI := GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one (l := l) (k := k)
  have h := fin_gen (γ := Wc.pd l k 1) (p := l) (κ := (Wc.res l k 1).comp ρ) hI (Fact.out : l.Prime).ne_zero hn U r j
  exact h

end GlobalTheory.CompanionTheory.FibGr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.WordIrr

theorem exists_lift_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) {H : Subgroup G} {y : W} (hy : y ∈ twKer τ H 1) :
    ∃ x ∈ twKer σ H 1, f x = y := by
  have hint : ∀ (g : G) (u : V), f.toLinearMap (σ g u) = τ g (f.toLinearMap u) :=
    fun g u => LinearMap.congr_fun (f.isIntertwining' g) u
  have hfL : ∀ x, f x = f.toLinearMap x := fun _ => rfl
  have hy' : y ∈ Submodule.span ℂ {w | ∃ (n : H) (v : W), w = τ ↑n v - ↑((1 : H →* ℂˣ) n) • v} := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, v, rfl⟩ := hw
    obtain ⟨u, rfl⟩ := hf v
    refine ⟨σ ↑n u - ↑((1 : H →* ℂˣ) n) • u, Submodule.subset_span ⟨n, u, rfl⟩, ?_⟩
    simp only [hfL, map_sub, Units.smul_def, map_smul, hint]
  | zero =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    rw [hfL]
    exact map_zero _
  | add a b _ _ ha hb =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    obtain ⟨x2, hx2, rfl⟩ := hb
    refine ⟨x1 + x2, add_mem hx1 hx2, ?_⟩
    simp only [hfL, map_add (f := _)]
  | smul c a _ ha =>
    obtain ⟨x1, hx1, rfl⟩ := ha
    refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
    simp only [hfL, map_smul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {V U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]

theorem jhMult_jac_of_le (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {S T : Subrepresentation π} (h : T ≤ S) :
    jhMult σ (GlobalTheory.SmGL.jac e S.toRepresentation) =
      jhMult σ (GlobalTheory.SmGL.jac e T.toRepresentation) + jhMult σ (GlobalTheory.SmGL.jac e (subQuot S T)) := by
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective j Subtype.val_injective).isSmooth hπ
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion h, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacquetExact.jacMap_injective e hS ι (Submodule.inclusion_injective h))
    (GlobalTheory.JacquetExact.jacMap_surjective e p hps) (fun u => ?_) (fun v hv => ?_)
  · obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have h0 : p (ι t) = 0 := (hp _).2 t.2
    show Submodule.Quotient.mk (p (ι t)) = 0
    rw [h0]
    rfl
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    have h1 : p x ∈ twKer (subQuot S T) (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
    obtain ⟨y, hy, hxy⟩ := exists_lift_twKer p hps h1
    have h2 : (x - y).1 ∈ T.toSubmodule := (hp _).1 (by rw [map_sub, hxy, sub_self])
    refine ⟨Submodule.Quotient.mk ⟨(x - y).1, h2⟩, ?_⟩
    show Submodule.Quotient.mk (x - y) = Submodule.Quotient.mk x
    refine (Submodule.Quotient.eq _).2 ?_
    rw [sub_sub_cancel_left]
    exact neg_mem hy

theorem exists_irrRep_of_subrep (e : (Σ a, Fin (d a)) ≃ Fin N)
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) U} (hσ : σ.IsIrreducible)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) (hl : HasFiniteLength π)
    (S : Subrepresentation π) (hS : jhMult σ (GlobalTheory.SmGL.jac e S.toRepresentation) ≠ 0) :
    ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ S.toRepresentation ∧ jhMult σ (GlobalTheory.SmGL.jac e τ.ρ) ≠ 0 := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hl
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  induction S using WellFoundedLT.induction with
  | ind S ih =>
  rcases eq_or_ne S ⊥ with rfl | hne
  · exfalso
    apply hS
    have h0 : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
      inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
    have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation π).toRepresentation (unipRad k e)) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton hσ _
  obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
  let ι : T.toRepresentation.IntertwiningMap S.toRepresentation := ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  let j : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  rw [jhMult_jac_of_le e hσ hπ hT.le] at hS
  by_cases h0 : jhMult σ (GlobalTheory.SmGL.jac e T.toRepresentation) = 0
  · rw [h0, zero_add] at hS
    have hq : IsSubquotient (subQuot S T) S.toRepresentation :=
      .of_surjective p (Submodule.Quotient.mk_surjective _)
    have hsm : IsSmooth (subQuot S T) :=
      (hq.trans (.of_injective j Subtype.val_injective)).isSmooth hπ
    exact ⟨⟨_, subQuot S T, hsm, isIrreducible_subQuot hT⟩, hq, hS⟩
  · obtain ⟨τ, h1, h2⟩ := ih T hT.lt h0
    exact ⟨τ, h1.trans (.of_injective ι (Submodule.inclusion_injective hT.le)), h2⟩

theorem exists_irrRep_wd : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL (k := k)), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  intro k _ _ _ _ hA N V _ _ π hπ hl w ⟨hd, hw⟩
  have hσ : (piTensor fun a => (w.get a).rep).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (w.get a).2.rep.irr) fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin (w.get a).1)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO _ _ (w.get a).2.rep.irr
        (hA k _ _ _ (w.get a).2.rep.smooth (w.get a).2.rep.irr) φ hφ
  have hT1 : IsSubquotient π (⊤ : Subrepresentation π).toRepresentation :=
    .of_surjective (topEquiv π).toIntertwiningMap (topEquiv π).surjective
  have hT2 : IsSubquotient (⊤ : Subrepresentation π).toRepresentation π :=
    .of_injective (topEquiv π).toIntertwiningMap (topEquiv π).injective
  have h1 : jhMult (piTensor fun a => (w.get a).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => (w.get a).1) hd) (⊤ : Subrepresentation π).toRepresentation) ≠ 0 :=
    jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 hw).trans
      (GlobalTheory.JacquetExact.isSubquotient_jac _ (hT2.isSmooth hπ) hT1))
  obtain ⟨τ, h2, h3⟩ := exists_irrRep_of_subrep _ hσ hπ hl ⊤ h1
  exact ⟨τ, h2.trans hT2, hd, h3⟩

end GlobalTheory.CompanionTheory.WordIrr

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotal
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {p : ℕ}

theorem mx_zero_subsingleton : Subsingleton (Mx D 0 p) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

theorem one_mem_schwartzA_zero (θ : InfFam D) : (fun _ => 1 : Mx D 0 p → ℂ) ∈ schwartzA θ 0 p := by
  refine Submodule.subset_span ?_
  let f : SchwartzMap (D.what₂.Tau → Fin 0 → Fin p → ℂ) ℂ :=
    { toFun := fun _ => 1
      smooth' := contDiff_const
      decay' := by
        intro k n
        refine ⟨1, fun x => ?_⟩
        have hx : x = 0 := Subsingleton.elim _ _
        subst hx
        rcases k with _ | k
        · rcases n with _ | n
          · simp
          · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
        · simp }
  refine ⟨f, fun _ => 1, ⟨IsLocallyConstant.const 1, ?_⟩, ?_⟩
  · exact (Set.subsingleton_of_subsingleton).isCompact
  · funext x
    exact (mul_one (1 : ℂ)).symm

theorem pr_zero (b₀ : HermE D 0) (x y : Mx D 0 p) : pr b₀ x y = 0 := by
  ext i j
  simp [pr, HMul.hMul]

theorem isTh_one {μ : Measure (Mx D 0 p)} (h1 : μ Set.univ = 1) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (b₀ : HermE D 0) : IsTh ψ 1 θ b₀ μ (fun _ _ => 1) := by
  have : IsProbabilityMeasure μ := ⟨h1⟩
  refine ⟨fun _ => one_mem_schwartzA_zero θ, continuous_const, ?_, ?_, ?_, ?_⟩
  · intro C _
    exact ⟨_, one_mem_schwartzA_zero θ, fun _ _ _ => le_rfl⟩
  · intro g a _ h y
    simp [npow]
  · intro g b _ h y
    simp [pr_zero, halfTr]
  · intro g _ h x
    simp [pr_zero]

theorem zeroTotal : ZeroTotal := by
  intro D p μ 𝓕 h ψ hψ b₀ θ hθ u hu hB hall
  have hs : Subsingleton (Mx D 0 p) := mx_zero_subsingleton
  obtain ⟨-, -, hF⟩ := h
  have hne : 𝓕.Nonempty := by
    rcases Set.eq_empty_or_nonempty 𝓕 with he | hn
    · simp [he] at hF
    · exact hn
  have huniv : 𝓕 = Set.univ := by
    obtain ⟨y, hy⟩ := hne
    exact Set.eq_univ_of_forall fun z => (Subsingleton.elim z y) ▸ hy
  have h1 : μ Set.univ = 1 := huniv ▸ hF
  have : IsProbabilityMeasure μ := ⟨h1⟩
  have h0 := hall _ (isTh_one h1 ψ θ b₀)
  have hc : (fun y => u y * conj (1 : ℂ)) = fun _ => u 0 := by
    funext y
    simp [Subsingleton.elim y 0]
  have h2 : u 0 = 0 := by
    have h3 : ∫ y, u y * conj (1 : ℂ) ∂μ = 0 := h0
    rw [hc] at h3
    simpa using h3
  funext y
  rw [Subsingleton.elim y 0, h2]
  rfl

end GlobalTheory.CompanionTheory.ThTot

end
end

