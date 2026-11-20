import CorralFormalization.EndpointProof.Matching.UniversalCore.FromSupplies
import CorralFormalization.EndpointProof.Matching.UniversalCore.BufferMatching
import CorralFormalization.EndpointProof.Matching.UniversalCore.QuadraticCapacityBudget
import CorralFormalization.EndpointProof.Flow.Tetrahedron.Sensitivity
import CorralFormalization.EndpointProof.Flow.Tetrahedron.SectionExpectation
import CorralFormalization.EndpointProof.Matching.UniversalCore.PairedCoverProperties
import CorralFormalization.EndpointProof.Matching.UniversalCore.Buffer.CoreTail

/-!
Construction of a fixed universal core after each forbidden set and before
every subsequent admissible residual. The selection graph and the common
sample event, including tetrahedron, buffer, selector and pair-count supplies,
are proved in the imported modules. The exact matching and the endpoint theorem
require further results beyond this core construction.
-/
