"""Axiomander exception hierarchy for contract violations and implementation placeholders."""


class AxiomanderError(Exception):
    """Root exception for all Axiomander-related errors."""
    pass


class ContractViolationError(AxiomanderError):
    """Base class for all contract violation errors."""
    
    def __init__(self, message: str, component_name: str = None, contract_text: str = None):
        """Initialize contract violation error.
        
        Args:
            message: Error message
            component_name: Name of the component where violation occurred
            contract_text: Text of the violated contract
        """
        self.component_name = component_name
        self.contract_text = contract_text
        super().__init__(message)


class PreconditionViolationError(ContractViolationError):
    """Raised when a precondition contract is violated."""
    
    def __init__(self, component_name: str, contract_text: str, args=None, kwargs=None):
        """Initialize precondition violation error.
        
        Args:
            component_name: Name of the component
            contract_text: Text of the violated precondition
            args: Function arguments that caused the violation
            kwargs: Function keyword arguments that caused the violation
        """
        message = f"Precondition violated in {component_name}: {contract_text}"
        if args is not None or kwargs is not None:
            message += f" (called with args={args}, kwargs={kwargs})"
        super().__init__(message, component_name, contract_text)
        self.args_passed = args
        self.kwargs_passed = kwargs


class PostconditionViolationError(ContractViolationError):
    """Raised when a postcondition contract is violated."""
    
    def __init__(self, component_name: str, contract_text: str, result=None, args=None, kwargs=None):
        """Initialize postcondition violation error.
        
        Args:
            component_name: Name of the component
            contract_text: Text of the violated postcondition
            result: Return value that caused the violation
            args: Function arguments
            kwargs: Function keyword arguments
        """
        message = f"Postcondition violated in {component_name}: {contract_text}"
        if result is not None:
            message += f" (returned {result})"
        super().__init__(message, component_name, contract_text)
        self.result = result
        self.args_passed = args
        self.kwargs_passed = kwargs


class InvariantViolationError(ContractViolationError):
    """Raised when an invariant contract is violated."""
    
    def __init__(self, component_name: str, contract_text: str, instance=None):
        """Initialize invariant violation error.
        
        Args:
            component_name: Name of the component (class)
            contract_text: Text of the violated invariant
            instance: Object instance that violated the invariant
        """
        message = f"Invariant violated in {component_name}: {contract_text}"
        super().__init__(message, component_name, contract_text)
        self.instance = instance


class ImplementationPlaceholderError(AxiomanderError):
    """Base class for implementation placeholder errors."""
    pass


class ImplementThisError(ImplementationPlaceholderError):
    """Raised when code reaches an 'implement this' placeholder.
    
    This indicates that a function or method needs to be implemented
    but currently contains only a placeholder.
    """
    
    def __init__(self, component_name: str = None, message: str = None):
        """Initialize implement this error.
        
        Args:
            component_name: Name of the component that needs implementation
            message: Optional custom message
        """
        if message is None:
            if component_name:
                message = f"Implementation required for {component_name}"
            else:
                message = "Implementation required - replace this placeholder"
        super().__init__(message)
        self.component_name = component_name


class DontImplementThisError(ImplementationPlaceholderError):
    """Raised when code reaches a 'don't implement this' placeholder.
    
    This indicates that a function or method should not be implemented
    in the current context (e.g., abstract methods, interface definitions).
    """
    
    def __init__(self, component_name: str = None, message: str = None):
        """Initialize don't implement this error.
        
        Args:
            component_name: Name of the component that should not be implemented
            message: Optional custom message
        """
        if message is None:
            if component_name:
                message = f"Implementation not allowed for {component_name} - this should remain abstract"
            else:
                message = "Implementation not allowed - this should remain abstract"
        super().__init__(message)
        self.component_name = component_name


class UnimplementedError(ImplementationPlaceholderError):
    """Raised when code reaches an unimplemented placeholder.
    
    This is a general placeholder for functionality that has not yet
    been implemented but is planned for future development.
    """
    
    def __init__(self, component_name: str = None, message: str = None):
        """Initialize unimplemented error.
        
        Args:
            component_name: Name of the component that is unimplemented
            message: Optional custom message
        """
        if message is None:
            if component_name:
                message = f"Functionality not yet implemented for {component_name}"
            else:
                message = "Functionality not yet implemented"
        super().__init__(message)
        self.component_name = component_name


# Convenience functions for raising placeholder errors
def implement_this(component_name: str = None, message: str = None) -> None:
    """Raise an ImplementThisError with optional context."""
    raise ImplementThisError(component_name, message)


def dont_implement_this(component_name: str = None, message: str = None) -> None:
    """Raise a DontImplementThisError with optional context."""
    raise DontImplementThisError(component_name, message)


def unimplemented(component_name: str = None, message: str = None) -> None:
    """Raise an UnimplementedError with optional context."""
    raise UnimplementedError(component_name, message)
