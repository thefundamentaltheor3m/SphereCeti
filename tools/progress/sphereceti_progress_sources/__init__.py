"""Access the inactive upstream source bundle without importing its implementation."""
from importlib.resources import files


def source_root():
    """Return packaged source resources; this does not install a reporting command."""
    return files(__package__).joinpath("sources")
